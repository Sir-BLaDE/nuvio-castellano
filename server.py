# -*- coding: utf-8 -*-
"""
NUVIO ADDON - AGREGADOR MULTI-FUENTE con filtro estricto de CASTELLANO
======================================================================

Protocolo: Stremio Addon (compatible con Nuvio)
- GET /manifest.json
- GET /{config}/manifest.json       (config = JSON base64url con la key de AllDebrid)
- GET /configure                    (pagina para introducir la key)
- GET /stream/movie/{imdb_id}.json
- GET /stream/series/{imdb_id}:{season}:{episode}.json

FUENTES que consulta en paralelo:
  1. Spanish Streams  - etiqueta explicitamente Castellano / Latino
  2. Torrentio (proveedores es: MejorTorrent, Cinecalidad, Wolfmax4k, ...)
  3. Peerflix         - la que ya tienes instalada
  4. Pipe             - scraping adicional de indices
  5. LatinoBox-ES     - configurado con langMode=only_castellano
  6. TorrentClaw      - modo INSTANT + AllDebrid (URL que redirige a debrid.it)
  7. Comet (ElfHosted)- cachedOnly + AllDebrid, solo marcas [AD⚡]

Descartadas tras investigacion: DeepFlix (directo propio, idioma "🇪🇸?" ambiguo),
Meteor (no distingue castellano de latino), TorrentsDB (sin marcadores de idioma
y sus enlaces son "AD download", no INSTANT) y AnimES/AnimeES (HTTP propio,
sin cache AllDebrid).

Pipeline:
  Consulta paralela -> filtro CASTELLANO (descarta latino/otros) ->
  deduplicacion por infoHash -> clasificacion detallada de calidad ->
  orden de mejor a peor -> conversion SOLO de magnets YA CACHEADOS en AllDebrid
  (flag `ready:true` en /magnet/upload + statusCode 4) ->
  SALIDA FINAL: unicamente streams con `url` directa. CERO P2P/magnets.

Sin dependencias externas (solo Python stdlib).
"""

import json
import re
import os
import time
import base64
import hashlib
import threading
import urllib.request
import urllib.parse
import urllib.error
from concurrent.futures import ThreadPoolExecutor, as_completed
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from typing import List, Dict, Any, Optional, Tuple, Callable

# =====================================================
# CONFIGURACION GENERAL
# =====================================================

ADDON_ID = "com.sirblade.nuvio-castellano"
ADDON_VERSION = "3.2.2"
ADDON_NAME = "Castellano ES - SOLO CACHE (Nuvio)"
ADDON_DESCRIPTION = (
    "Agrega Spanish Streams + Torrentio(ES) + Peerflix + Pipe + LatinoBox-ES "
    "+ TorrentClaw + Comet. SOLO castellano espanol (descarta latino/otros "
    "idiomas) y SOLO enlaces directos YA CACHEADOS en AllDebrid: cero "
    "magnets/P2P. Ordenados por calidad: Remux > BluRay > WEB-DL > HDTV."
)

HOST = "0.0.0.0"
PORT = 7000
# URL publica real (Beamup reescribe el header Host a un nombre interno).
# Se puede cambiar con la variable de entorno PUBLIC_ADDON_URL.
PUBLIC_ADDON_URL = os.environ.get(
    "PUBLIC_ADDON_URL", "https://806399bc52d4-nuvio-castellano.baby-beamup.club"
).rstrip("/")

ALLDEBRID_API = "https://api.alldebrid.com/v4"
ALLDEBRID_USER_ENDPOINT = f"{ALLDEBRID_API}/user"
ALLDEBRID_MAGNET_UPLOAD = f"{ALLDEBRID_API}/magnet/upload"
ALLDEBRID_MAGNET_STATUS = "https://api.alldebrid.com/v4.1/magnet/status"
ALLDEBRID_LINK_UNLOCK = f"{ALLDEBRID_API}/link/unlock"
ALLDEBRID_AGENT = "NuvioCastellanoAddon"

# Calidad minima (40 = 720p). Subir a 60 para exigir 1080p+
MIN_QUALITY_SCORE = 40

# Convertir TODOS los candidatos a enlaces directos. Solo se devuelven los que
# AllDebrid confirma como YA cacheados (ready:true). 0 = sin limite.
MAX_DIRECT_LINKS = 0

# Numero de llamadas concurrentes a la API de AllDebrid
MAX_AD_WORKERS = 8

# Caché
CACHE_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "cache")
STREAM_CACHE_FILE = os.path.join(CACHE_DIR, "streams.json")
DIRECT_CACHE_FILE = os.path.join(CACHE_DIR, "direct.json")
STREAM_CACHE_TTL = 600        # 10 minutos
DIRECT_CACHE_TTL = 86400      # 24 horas

_cache_lock = threading.Lock()


# =====================================================
# DEFINICION DE FUENTES
# =====================================================

TORRENTIO_PROVIDERS = (
    "mejortorrent,cinecalidad,wolfmax4k,besttorrents,torrent9,comando,bludv,"
    "yts,1337x,tpb,rarbg,eztv,torrentgalaxy,magnetdl,kickasstorrents"
)

def _latinobox_config(lang_mode: str = "only_castellano") -> str:
    """Config base64url de LatinoBox forzando SOLO castellano."""
    cfg = {
        "userKey": "usr_p2p_70a86304bc23e0226f7",
        "torboxApiKey": "",
        "resolutions": ["2160p", "1080p", "720p", "480p"],
        "maxSizeGB": 120,
        "allowCam": False,
        "onlyCached": False,
        "langMode": lang_mode,
    }
    raw = json.dumps(cfg, separators=(",", ":")).encode("utf-8")
    return base64.urlsafe_b64encode(raw).decode("ascii").rstrip("=")


_TC_CONFIG_CACHE: Dict[str, str] = {}


def _torrentclaw_base(key: str, timeout: int = 12) -> str:
    """
    Construye (una vez por key) la URL cifrada de TorrentClaw con AllDebrid.
    El token de debrid queda cifrado en el servidor de TorrentClaw: no viaja
    en claro en la URL publica del addon.
    """
    fp = _fingerprint(key)
    if fp in _TC_CONFIG_CACHE:
        return _TC_CONFIG_CACHE[fp]

    body = {
        "prefs": {
            "lang": "es-ES",
            "langHard": True,
            "langOnly": True,
            "vo": True,
            "noP2P": True,
            "noDebrid": False,
            "noUnarr": True,
            "noCatalogs": True,
            "sort": "score",
        },
        "debrid": {"provider": "alldebrid", "token": key},
    }
    req = urllib.request.Request(
        "https://torrentclaw.com/api/stremio/configure/build",
        data=json.dumps(body, separators=(",", ":")).encode("utf-8"),
        headers={"Content-Type": "application/json", "Accept": "application/json",
                 "User-Agent": f"{ALLDEBRID_AGENT}/2.0"},
        method="POST",
    )
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        data = json.loads(resp.read().decode("utf-8"))
    manifest = data.get("manifestUrl", "")
    suffix = "/manifest.json"
    if not manifest.endswith(suffix):
        raise ValueError("TorrentClaw no devolvio manifestUrl")
    base = manifest[: -len(suffix)]
    _TC_CONFIG_CACHE[fp] = base
    return base


def _comet_base(key: str) -> str:
    """Config de Comet: cachedOnly + AllDebrid + idioma es (base64 estandar)."""
    settings = {
        "debridServices": [{"service": "alldebrid", "apiKey": key}],
        "enableTorrent": False,
        "cachedOnly": True,
        "deduplicateStreams": True,
        "languages": {"required": ["es"], "allowed": ["es"], "exclude": [], "preferred": ["es"]},
        "options": {
            "remove_ranks_under": 0,
            "allow_english_in_languages": False,
            "remove_unknown_languages": True,
        },
        "resultFormat": ["all"],
    }
    for sep in ((",", ":"), (", ", ": "), (",", ": ")):
        raw = json.dumps(settings, separators=sep).encode("utf-8")
        b64 = base64.b64encode(raw).decode("ascii")
        if "/" not in b64:  # '/' romperia el path del addon
            return f"https://comet.elfhosted.com/{b64}"
    raise ValueError("No se pudo codificar la configuracion de Comet sin '/'")


SOURCES: Dict[str, Dict[str, Any]] = {
    "spanishstreams": {
        "label": "SpanishStreams",
        "build": lambda t, i, k: (
            f"https://965d83ef8484-stremio-latino.baby-beamup.club"
            f"/stream/{t}/{urllib.parse.quote(i, safe=':')}.json"
        ),
    },
    "torrentio_es": {
        "label": "Torrentio-ES",
        "build": lambda t, i, k: (
            f"https://torrentio.strem.fun/language=es%7Cproviders={TORRENTIO_PROVIDERS}"
            f"/stream/{t}/{urllib.parse.quote(i, safe=':')}.json"
        ),
    },
    "peerflix": {
        "label": "Peerflix",
        "build": lambda t, i, k: (
            f"https://addon.peerflix.mov/stream/{t}/{urllib.parse.quote(i, safe=':')}.json?"
            + urllib.parse.urlencode({
                "language": "es",
                "debridoptions": "nocatalog",
                "sort": "language-desc",
                **({"alldebrid": k} if k else {}),
            })
        ),
    },
    "pipe": {
        "label": "Pipe",
        "build": lambda t, i, k: (
            f"https://pipe.boringways.workers.dev"
            f"/stream/{t}/{urllib.parse.quote(i, safe=':')}.json"
        ),
    },
    "latinobox": {
        "label": "LatinoBox-ES",
        "build": lambda t, i, k: (
            f"https://latinobox.daleplay.biz/c/{_latinobox_config()}"
            f"/stream/{t}/{urllib.parse.quote(i, safe=':')}.json"
        ),
    },
    "torrentclaw": {
        "label": "TorrentClaw-AD",
        "build": lambda t, i, k: (
            f"{_torrentclaw_base(k)}/stream/{t}/{urllib.parse.quote(i, safe=':')}.json"
        ),
    },
    "comet": {
        "label": "Comet-AD",
        "build": lambda t, i, k: (
            f"{_comet_base(k)}/stream/{t}/{urllib.parse.quote(i, safe=':')}.json"
        ),
    },
}

DEFAULT_SOURCES = list(SOURCES.keys())


# =====================================================
# CACHÉ EN DISCO
# =====================================================

def _load_cache(path: str) -> Dict[str, Any]:
    try:
        with open(path, "r", encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return {}


def _save_cache(path: str, data: Dict[str, Any]) -> None:
    try:
        os.makedirs(CACHE_DIR, exist_ok=True)
        tmp = path + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False)
        os.replace(tmp, path)
    except Exception as e:
        print(f"[WARN] No se pudo guardar cache: {e}")


def _cache_get(path: str, key: str, ttl: int) -> Optional[Any]:
    with _cache_lock:
        data = _load_cache(path)
    entry = data.get(key)
    if not entry:
        return None
    if time.time() - entry.get("ts", 0) > ttl:
        return None
    return entry.get("value")


def _cache_set(path: str, key: str, value: Any) -> None:
    with _cache_lock:
        data = _load_cache(path)
        data[key] = {"ts": time.time(), "value": value}
        # Limitar tamano: conservar solo las 500 entradas mas recientes
        if len(data) > 500:
            items = sorted(data.items(), key=lambda kv: kv[1].get("ts", 0), reverse=True)
            data = dict(items[:500])
        _save_cache(path, data)


def _cache_set_many(path: str, items: List[Tuple[str, Any]]) -> None:
    """Guarda varias entradas de cache con una sola lectura/escritura de disco."""
    if not items:
        return
    with _cache_lock:
        data = _load_cache(path)
        now = time.time()
        for key, value in items:
            data[key] = {"ts": now, "value": value}
        if len(data) > 500:
            ordered = sorted(data.items(), key=lambda kv: kv[1].get("ts", 0), reverse=True)
            data = dict(ordered[:500])
        _save_cache(path, data)


def _fingerprint(key: str) -> str:
    """Huella de la key (nunca se guarda la key en claro en la cache)."""
    return hashlib.sha256(key.encode("utf-8")).hexdigest()[:12] if key else "nokey"


# =====================================================
# FILTRADO DE IDIOMA - CASTELLANO ESTRICTO
# =====================================================

ES_MARKERS = [
    "🇪🇸", "castellano", "español", "espanol", "spanish",
    "es-es", "vo.es", "[es]", "(es)", "audio: es", "cast",
]
LATIN_MARKERS = [
    "🇲🇽", "🇦🇷", "🇨🇴", "🇨🇱", "🇵🇪", "latino", "latín",
    "mexicano", "argentino", "colombiano", "es-mx", "es-ar", "es-co",
]
OTHER_MARKERS = [
    "🇮🇹", "🇫🇷", "🇩🇪", "🇵🇹", "🇷🇺", "🇯🇵", "🇰🇷", "🇨🇳",
    "italiano", "frances", "français", "deutsch", "portugués", "portuguese", "ruso",
]

LANG_RANK = {
    "CASTELLANO": 3,
    "CASTELLANO_DUAL": 2,   # tiene castellano + latino (audio dual)
    "LATINO": 1,
    "OTRO": 0,
    "SIN_MARCADOR": 0,
}

LANG_LABEL = {
    "CASTELLANO": "CASTELLANO",
    "CASTELLANO_DUAL": "CASTELLANO+Latino",
}


def classify_language(stream: Dict[str, Any]) -> str:
    """
    Clasifica el idioma del stream.
    El bingeGroup de Spanish Streams es autoritativo (castellano|latino).
    """
    title = stream.get("title", "") or ""
    name = stream.get("name", "") or ""
    desc = stream.get("description", "") or ""   # Meteor/AnimES usan 'description'
    group = ""
    try:
        group = stream.get("behaviorHints", {}).get("bingeGroup", "") or ""
    except Exception:
        pass

    text = f"{title} {desc} {name} {group}".lower()
    group_lower = group.lower()

    # 1) Fuente que etiqueta explicitamente
    if "spanishstreams|castellano" in group_lower:
        return "CASTELLANO_DUAL" if "latino" in text else "CASTELLANO"
    if "spanishstreams|latino" in group_lower:
        return "LATINO"

    # 2) Analisis del titulo
    has_es = any(m.lower() in text for m in ES_MARKERS)
    has_lat = any(m.lower() in text for m in LATIN_MARKERS)
    has_other = any(m.lower() in text for m in OTHER_MARKERS)

    # Marcadores dudosos tipo "🇪🇸?" / "ES?" no cuentan como castellano confirmado.
    ambiguo = ("🇪🇸?" in text) or bool(re.search(r"\bes\?", text))
    if ambiguo and not re.search(r"castellano|español|espanol|vo\.es|es-es", text):
        return "LATINO" if has_lat else "SIN_MARCADOR"

    # Audio dual castellano+latino: se mantiene pero se ordena despues del
    # castellano puro (no es lo que se ve en el nombre de LatinoBox-ES).
    if has_lat and has_es:
        return "CASTELLANO_DUAL"
    if has_es:
        return "CASTELLANO"
    if has_lat:
        return "LATINO"
    if has_other:
        return "OTRO"
    return "SIN_MARCADOR"


# =====================================================
# CLASIFICACION DETALLADA DE CALIDAD
# =====================================================

# La resolucion se lee SOLO de marcadores explicitos (palabra completa).
# "4Kreescalado", "4kids" o una etiqueta del proveedor no cuentan como 4K si
# el fichero dice 720p/480p.
_RESOLUTION_SCORES = {
    2160: 85, 1080: 60, 720: 40, 576: 30, 480: 30,
}
_TYPE_SCORES = {
    "REMUX": 15, "BluRay": 10, "WEB-DL": 5, "HDTV": 5,
    "DVD Rip": -5, "CAM/TS": -30, "": 0,
}
_TYPE_LABEL = {
    "REMUX": "REMUX", "BluRay": "BluRay", "WEB-DL": "WEB-DL",
    "HDTV": "HDTV", "DVD Rip": "DVD Rip", "CAM/TS": "CAM/TS", "": "",
}


def _detect_resolution(t: str) -> int:
    explicit = [int(x[:-1]) for x in re.findall(r"\b(2160p|1080p|720p|576p|480p)\b", t)]
    if explicit:
        return max(explicit)
    if re.search(r"\b(4k|uhd)\b", t):
        return 2160
    return 0


def _detect_type(t: str) -> str:
    if re.search(r"remux", t):
        return "REMUX"
    if re.search(r"blu ?ray|bluray|bdrip|brrip", t):
        return "BluRay"
    if re.search(r"web-?dl|webdl", t):
        return "WEB-DL"
    if re.search(r"hdtv|tvrip", t):
        return "HDTV"
    if re.search(r"dvd ?rip|dvdrip", t):
        return "DVD Rip"
    if re.search(r"\bcam\b|\bts\b|screener", t):
        return "CAM/TS"
    return ""


def classify_quality(title: str) -> Tuple[int, str]:
    """Devuelve (score, etiqueta) usando la resolucion REAL del fichero."""
    t = (title or "").lower()
    res = _detect_resolution(t)
    kind = _detect_type(t)

    if res:
        res_txt = "4K UHD" if res == 2160 else f"{res}p"
        score = _RESOLUTION_SCORES[res] + _TYPE_SCORES[kind]
        label = f"{res_txt} {_TYPE_LABEL[kind]}".strip()
    elif kind in ("DVD Rip", "CAM/TS"):
        score, label = (25, "DVD Rip") if kind == "DVD Rip" else (10, "CAM/TS")
    else:
        score, label = 0, "DESCONOCIDA"

    bonus = 0
    if re.search(r"\bhdr10\b|\bhdr\b|dolby vision|\bdv\b", t):
        bonus += 3
    if re.search(r"\batmos\b|dts-hd|truehd|dts 5\.1", t):
        bonus += 2
    if re.search(r"remaster|restaurad|remasterizada", t):
        bonus += 1
    return score + bonus, label


def extract_seeds(title: str) -> int:
    m = re.search(r"👤\s*(\d+)", title or "")
    return int(m.group(1)) if m else 0


def extract_size_gb(title: str) -> float:
    m = re.search(r"💾\s*([\d.]+)\s*(GB|MB)", title or "", re.IGNORECASE)
    if m:
        v = float(m.group(1))
        return v if m.group(2).upper() == "GB" else v / 1024
    return 0.0


# =====================================================
# CONSULTA PARALELA A FUENTES
# =====================================================

def _fetch_source(source_id: str, url: str, timeout: int = 18) -> Tuple[str, List[Dict[str, Any]], Optional[str]]:
    try:
        req = urllib.request.Request(
            url,
            headers={
                "User-Agent": f"{ALLDEBRID_AGENT}/2.0",
                "Accept": "application/json",
            },
        )
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            data = json.loads(resp.read().decode("utf-8"))
        streams = data.get("streams", []) if isinstance(data, dict) else []
        return source_id, streams if isinstance(streams, list) else [], None
    except Exception as e:
        return source_id, [], str(e)


def _filter_cached_direct(source_id: str, streams: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    """
    Las fuentes que ya entregan URL propia solo se aceptan si ellas mismas
    garantizan cache AllDebrid (INSTANT / [AD⚡]). El resto se descarta.
    """
    kept: List[Dict[str, Any]] = []
    for raw in streams:
        if not isinstance(raw, dict):
            continue
        s = dict(raw)
        if source_id == "torrentclaw":
            name = s.get("name", "") or ""
            title = s.get("title", "") or ""
            if (
                "INSTANT" not in name.upper()
                or "AD" not in title.upper()
                or "caches on play" in title.lower()
            ):
                continue
            s["_verified_cached"] = True
        elif source_id == "comet":
            if not (s.get("name", "") or "").startswith("[AD⚡]"):
                continue
            s["_verified_cached"] = True
        kept.append(s)
    return kept


def fetch_all_sources(
    media_type: str,
    full_id: str,
    alldebrid_key: str,
    enabled_sources: List[str],
) -> Tuple[List[Tuple[str, Dict[str, Any]]], Dict[str, str]]:
    """Consulta todas las fuentes en paralelo. Devuelve (streams por fuente, errores)."""
    jobs = {}
    for sid in enabled_sources:
        src = SOURCES.get(sid)
        if not src:
            continue
        try:
            jobs[sid] = src["build"](media_type, full_id, alldebrid_key)
        except Exception as e:
            print(f"[WARN] No se pudo construir URL para {sid}: {e}")

    collected: List[Tuple[str, Dict[str, Any]]] = []
    errors: Dict[str, str] = {}

    with ThreadPoolExecutor(max_workers=max(1, len(jobs))) as pool:
        futures = {pool.submit(_fetch_source, sid, url): sid for sid, url in jobs.items()}
        for fut in as_completed(futures):
            sid, streams, err = fut.result()
            if err:
                errors[sid] = err
                print(f"[WARN] Fuente {sid} fallo: {err}")
            else:
                kept = _filter_cached_direct(sid, streams)
                print(f"[INFO] Fuente {sid}: {len(kept)}/{len(streams)} streams (cacheados)")
                for s in kept:
                    collected.append((sid, s))
    return collected, errors


# =====================================================
# FILTRADO + DEDUPLICACION + RANKING
# =====================================================

def _dedup_key(stream: Dict[str, Any]) -> str:
    h = stream.get("infoHash")
    if h:
        return f"hash:{str(h).lower()}"
    url = stream.get("url")
    if url:
        return f"url:{str(url)[:200]}"
    title = stream.get("title") or stream.get("description") or ""
    title = re.sub(r"\s+", " ", title).strip().lower()
    return f"title:{title[:160]}"


def build_rankings(
    raw: List[Tuple[str, Dict[str, Any]]],
    media_type: str = "movie",
) -> Tuple[List[Dict[str, Any]], Dict[str, int]]:
    """
    Filtra a castellano, deduplica y ordena de mejor a peor.
    Devuelve (streams rankeados, contadores de descarte).
    """
    stats: Dict[str, int] = {}
    best: Dict[str, Dict[str, Any]] = {}

    for source_id, stream in raw:
        lang = classify_language(stream)
        if lang not in ("CASTELLANO", "CASTELLANO_DUAL"):
            stats[lang] = stats.get(lang, 0) + 1
            continue

        title = stream.get("title") or stream.get("description") or ""

        # Comet solo etiqueta "es" generico: exigimos CASTELLANO explicito
        # en el nombre del fichero para no colar latino.
        if source_id == "comet" and not re.search(
            r"castellano|es-es|vo\.es", title, re.IGNORECASE
        ):
            stats["comet_sin_castellano"] = stats.get("comet_sin_castellano", 0) + 1
            continue

        # LatinoBox mezcla packs de temporada en resultados de episodio.
        if media_type == "series" and re.search(
            r"temporadas?|season|serie completa|cap[ií]tulos? complet|\bs\d{1,2}\s*(?:-|a)\s*s?\d{1,2}\b",
            title, re.IGNORECASE,
        ):
            stats["pack_temporada"] = stats.get("pack_temporada", 0) + 1
            continue

        # La resolucion real del fichero esta en `title`. Solo si no se puede
        # determinar se mira `name` (TorrentClaw/Meteor/Comet la ponen ahi).
        # Asi un "4K" de etiqueta nunca gana a un "720p" real del titulo.
        score, label = classify_quality(title)
        if score == 0 and label == "DESCONOCIDA":
            score, label = classify_quality(stream.get("name", "") or "")
        if score < MIN_QUALITY_SCORE:
            stats["calidad_baja"] = stats.get("calidad_baja", 0) + 1
            continue

        key = _dedup_key(stream)
        candidate = {
            "stream": stream,
            "lang": lang,
            "lang_rank": LANG_RANK[lang],
            "score": score,
            "label": label,
            "seeds": extract_seeds(title),
            "size": extract_size_gb(title),
            "sources": {SOURCES.get(source_id, {}).get("label", source_id)},
        }

        prev = best.get(key)
        if prev is None or _candidate_score(candidate) > _candidate_score(prev):
            if prev:
                candidate["sources"] |= prev["sources"]
            best[key] = candidate
        else:
            prev["sources"] |= candidate["sources"]

    ranked = sorted(best.values(), key=_candidate_score, reverse=True)

    result: List[Dict[str, Any]] = []
    for rank, c in enumerate(ranked, 1):
        s = dict(c["stream"])  # copia para no mutar la respuesta original
        fuentes = " + ".join(sorted(c["sources"]))
        lang_txt = LANG_LABEL[c["lang"]]
        s["name"] = f"#{rank} {lang_txt} | {c['label']} | {fuentes}"
        original_title = c["stream"].get("title") or c["stream"].get("description") or ""
        s["title"] = (
            f"[ES] {c['label']} · score {c['score']} · 👤{c['seeds']} · "
            f"💾{c['size']:.1f}GB · {fuentes}\n{original_title}"
        )
        result.append(s)

    print(f"[INFO] Castellanos tras filtro/dedup: {len(result)} | descartes: {stats}")
    return result, stats


def _candidate_score(c: Dict[str, Any]) -> Tuple[int, int, int, int, float]:
    return (
        c["lang_rank"],   # castellano puro primero
        c["score"],       # calidad
        c["seeds"],
        c["size"],
    )


# =====================================================
# ALLDEBRID: AUTH + CONVERSION MAGNET -> URL DIRECTA
# =====================================================

def validate_alldebrid_key(key: str) -> Tuple[bool, str]:
    if not key or not key.strip():
        return False, "No se introdujo ninguna clave"
    req = urllib.request.Request(
        ALLDEBRID_USER_ENDPOINT,
        headers={
            "Authorization": f"Bearer {key.strip()}",
            "User-Agent": ALLDEBRID_AGENT,
            "Accept": "application/json",
        },
    )
    try:
        with urllib.request.urlopen(req, timeout=15) as resp:
            data = json.loads(resp.read().decode("utf-8"))
        if data.get("status") == "success":
            user = data.get("data", {}).get("user", {})
            premium = "PREMIUM" if user.get("isPremium") else "FREE"
            return True, f"Clave valida (usuario: {user.get('username', 'usuario')}, cuenta {premium})"
        err = data.get("error", {})
        return False, f"Clave rechazada [{err.get('code', '')}]: {err.get('message', 'invalida')}"
    except urllib.error.HTTPError as e:
        return False, f"Error HTTP de AllDebrid: {e.code}"
    except urllib.error.URLError as e:
        return False, f"No se pudo contactar con AllDebrid: {e.reason}"
    except Exception as e:
        return False, f"Error validando clave: {e}"


def _ad_get(url: str, key: str) -> Optional[Dict[str, Any]]:
    try:
        req = urllib.request.Request(
            url,
            headers={
                "Authorization": f"Bearer {key}",
                "User-Agent": ALLDEBRID_AGENT,
                "Accept": "application/json",
            },
        )
        with urllib.request.urlopen(req, timeout=20) as resp:
            return json.loads(resp.read().decode("utf-8"))
    except Exception as e:
        print(f"[WARN] AllDebrid GET fallo: {e}")
        return None


def _ad_upload_magnet(hash_: str, key: str) -> Optional[Dict[str, Any]]:
    """
    Sube un hash a AllDebrid y devuelve el objeto magnet completo.

    El campo `ready` de esta respuesta es la señal de CACHE:
      ready = True  -> AllDebrid ya lo tiene, hay enlaces directos al instante.
      ready = False -> no esta cacheado (se descarta, nunca se ofrece P2P).
    """
    try:
        body = urllib.parse.urlencode({"magnets[]": hash_}).encode("utf-8")
        url = f"{ALLDEBRID_MAGNET_UPLOAD}?agent={ALLDEBRID_AGENT}&apikey={key}"
        req = urllib.request.Request(
            url,
            data=body,
            method="POST",
            headers={
                "Authorization": f"Bearer {key}",
                "Content-Type": "application/x-www-form-urlencoded",
                "User-Agent": ALLDEBRID_AGENT,
            },
        )
        with urllib.request.urlopen(req, timeout=25) as resp:
            data = json.loads(resp.read().decode("utf-8"))
        magnets = (data.get("data") or {}).get("magnets") or []
        if magnets and "id" in magnets[0]:
            return magnets[0]
        err = data.get("error", {})
        print(f"[WARN] AllDebrid upload: {err.get('code')} {err.get('message')}")
    except Exception as e:
        print(f"[WARN] AllDebrid upload fallo: {e}")
    return None


VIDEO_EXT = (".mkv", ".mp4", ".avi", ".mov", ".m4v", ".ts", ".webm", ".wmv", ".flv")
JUNK_EXT = (".txt", ".nfo", ".url", ".jpg", ".jpeg", ".png", ".sfv", ".exe", ".rar", ".zip")


def _pick_direct_link(magnet_files: List[Dict[str, Any]], file_idx: Optional[int]) -> Optional[Tuple[str, str]]:
    """Elige el archivo de video mas grande; ignora TXT/NFO/URLs promotionales."""
    candidates: List[Tuple[int, str, str]] = []
    for folder in magnet_files:
        for f in (folder.get("e") or []):
            link = f.get("l")
            if not link:
                continue
            filename = f.get("n", "") or ""
            low = filename.lower()
            if low.endswith(JUNK_EXT):
                continue
            size = int(f.get("s") or 0)
            candidates.append((size, filename, link))
    if not candidates:
        return None

    videos = [c for c in candidates if c[1].lower().endswith(VIDEO_EXT)]
    pool = videos or candidates
    pool.sort(reverse=True)  # mayor tamaño primero
    size, filename, link = pool[0]
    return filename, link


def _magnet_is_ready(mag: Dict[str, Any]) -> bool:
    """AllDebrid statusCode 4 = 'Ready'. Cualquier otro estado NO es cache."""
    try:
        return int(mag.get("statusCode", -1)) == 4
    except (TypeError, ValueError):
        return str(mag.get("status", "")).lower() == "ready"


def _make_direct_stream(stream: Dict[str, Any], direct_url: str, tag: str = "[CACHE]") -> Dict[str, Any]:
    """
    Construye el stream final SIN campos P2P.

    Se crea un dict nuevo: no se copian `infoHash`, `fileIdx` ni
    `behaviorHints.bingeGroup`. El unico campo de reproduccion es `url`.
    """
    name = stream.get("name", "") or "Stream"
    if tag not in name:
        name = f"{name} {tag}"
    return {
        "name": name,
        "title": stream.get("title", "") or "",
        "url": direct_url,
    }


def convert_to_direct_links(streams: List[Dict[str, Any]], key: str) -> List[Dict[str, Any]]:
    """
    Devuelve SOLAMENTE streams con URL directa cacheada en AllDebrid.

    Descarta:
      - streams sin key de AllDebrid,
      - magnets que AllDebrid no marca como `ready` (no cacheados),
      - magnets cuyo estado no sea statusCode 4,
      - enlaces que no se pueden desbloquear.

    Nunca devuelve `infoHash` ni `fileIdx`: el resultado es 100% no-P2P.
    """
    if not key:
        return []

    fp = _fingerprint(key)
    targets = streams if MAX_DIRECT_LINKS <= 0 else streams[:MAX_DIRECT_LINKS]
    results: List[Optional[Dict[str, Any]]] = [None] * len(targets)
    new_cache: List[Tuple[str, str]] = []

    def worker(idx: int, stream: Dict[str, Any]) -> None:
        # Algunas fuentes ya entregan URL directa cacheada (TorrentClaw/Comet).
        if stream.get("url") and not stream.get("infoHash"):
            tag = "[CACHE-AD]" if stream.get("_verified_cached") else "[DIRECTO]"
            results[idx] = _make_direct_stream(stream, stream["url"], tag)
            return

        hash_ = stream.get("infoHash")
        if not hash_:
            return

        cache_key = f"{fp}:{hash_}:{stream.get('fileIdx', 'x')}"
        cached = _cache_get(DIRECT_CACHE_FILE, cache_key, DIRECT_CACHE_TTL)
        if cached:
            results[idx] = _make_direct_stream(stream, cached)
            return

        uploaded = _ad_upload_magnet(hash_, key)
        if not uploaded:
            return
        if not uploaded.get("ready"):
            # NO cacheado: se descarta. Nunca se ofrece el magnet al usuario.
            return

        status = _ad_get(
            f"{ALLDEBRID_MAGNET_STATUS}?agent={ALLDEBRID_AGENT}"
            f"&apikey={key}&id={uploaded['id']}", key
        ) or {}
        magnets = (status.get("data") or {}).get("magnets")
        if isinstance(magnets, dict):
            magnets = [magnets]

        ready_magnets = [m for m in (magnets or []) if _magnet_is_ready(m)]
        if not ready_magnets:
            return

        magnet_files: List[Dict[str, Any]] = []
        for mag in ready_magnets:
            files = mag.get("files") or []
            if isinstance(files, list):
                magnet_files.extend(f for f in files if isinstance(f, dict))
        picked = _pick_direct_link(magnet_files, stream.get("fileIdx"))
        if not picked:
            return

        filename, ad_link = picked
        unlocked = _ad_get(
            f"{ALLDEBRID_LINK_UNLOCK}?agent={ALLDEBRID_AGENT}&apikey={key}"
            f"&link={urllib.parse.quote(ad_link, safe='')}", key
        ) or {}
        direct = (unlocked.get("data") or {}).get("link")
        if direct:
            results[idx] = _make_direct_stream(stream, direct)
            new_cache.append((cache_key, direct))
            print(f"[INFO] CACHE directo: {filename[:60]}")

    with ThreadPoolExecutor(max_workers=MAX_AD_WORKERS) as pool:
        futures = [pool.submit(worker, i, s) for i, s in enumerate(targets)]
        for fut in as_completed(futures):
            try:
                fut.result()
            except Exception as e:
                print(f"[WARN] Conversion AllDebrid fallo: {e}")

    _cache_set_many(DIRECT_CACHE_FILE, new_cache)
    final = [r for r in results if r is not None]
    # Renumerar: los que no estaban cacheados desaparecieron, no dejar huecos.
    for rank, s in enumerate(final, 1):
        s["name"] = re.sub(r"^#\d+", f"#{rank}", s["name"])
    descartados = len(targets) - len(final)
    print(f"[INFO] Cacheados: {len(final)}/{len(targets)} | descartados (P2P/no cache): {descartados}")
    return final


# =====================================================
# ORQUESTADOR PRINCIPAL
# =====================================================

def build_streams(
    media_type: str,
    full_id: str,
    alldebrid_key: str,
    enabled_sources: List[str],
) -> List[Dict[str, Any]]:
    fp = _fingerprint(alldebrid_key)
    cache_key = f"{media_type}|{full_id}|{','.join(enabled_sources)}|{fp}"

    cached = _cache_get(STREAM_CACHE_FILE, cache_key, STREAM_CACHE_TTL)
    if cached is not None:
        print(f"[INFO] Cache HIT: {full_id}")
        return cached

    raw, errors = fetch_all_sources(media_type, full_id, alldebrid_key, enabled_sources)
    ranked, _ = build_rankings(raw, media_type)

    if not alldebrid_key:
        print("[WARN] Sin API key de AllDebrid: este addon solo sirve enlaces cacheados")
        return []

    # Unico punto de salida: se sustituye la lista P2P por solo enlaces cacheados.
    final = convert_to_direct_links(ranked, alldebrid_key)
    print(f"[INFO] Resultado final 100% cacheado: {len(final)} streams (de {len(ranked)} candidatos)")

    _cache_set(STREAM_CACHE_FILE, cache_key, final)
    return final


# =====================================================
# CONFIGURACION (base64url) + MANIFIESTO
# =====================================================

def encode_config(cfg: Dict[str, Any]) -> str:
    raw = json.dumps(cfg, separators=(",", ":"), ensure_ascii=False).encode("utf-8")
    return base64.urlsafe_b64encode(raw).decode("ascii").rstrip("=")


def decode_config(config: str) -> Dict[str, Any]:
    if not config:
        return {}
    try:
        padding = "=" * (-len(config) % 4)
        raw = base64.urlsafe_b64decode(config + padding).decode("utf-8")
        data = json.loads(raw)
        return data if isinstance(data, dict) else {}
    except Exception:
        return {}


def build_manifest() -> Dict[str, Any]:
    return {
        "id": ADDON_ID,
        "version": ADDON_VERSION,
        "name": ADDON_NAME,
        "description": ADDON_DESCRIPTION,
        "catalogs": [],
        "resources": [{
            "name": "stream",
            "types": ["movie", "series"],
            "idPrefixes": ["tt", "kitsu", "tmdb"],
        }],
        "types": ["movie", "series"],
        "logo": "https://i.ibb.co/vL3SKgX/peerflix-background-2.jpg",
        "background": "https://i.ibb.co/vL3SKgX/peerflix-background-2.jpg",
        "behaviorHints": {
            "configurable": True,
            "configurationRequired": True,
        },
    }


# =====================================================
# PAGINA DE CONFIGURACION
# =====================================================

CONFIGURE_HTML = """<!DOCTYPE html>
<html lang="es">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Configurar {name}</title>
<style>
  body { font-family: system-ui, sans-serif; max-width: 720px; margin: 40px auto; padding: 20px; background:#121212; color:#eee; }
  h1 { color:#23CC98; }
  h2 { color:#23CC98; font-size:1.1rem; margin-top:28px; }
  input[type=text] { width:100%; padding:12px; font-size:16px; border-radius:6px; border:1px solid #444; background:#1e1e1e; color:#eee; box-sizing:border-box; }
  label { display:block; margin:10px 0 4px; color:#ccc; }
  button { margin-top:16px; padding:12px 24px; font-size:16px; background:#23CC98; color:#000; border:none; border-radius:6px; cursor:pointer; font-weight:bold; }
  #msg { margin-top:16px; padding:12px; border-radius:6px; display:none; }
  .ok { background:#1b3a2b; color:#7fe3a8; }
  .err { background:#3a1b1b; color:#ff9b9b; }
  code { background:#1e1e1e; padding:2px 6px; border-radius:4px; word-break:break-all; }
  .src { background:#1a1a1a; padding:10px 14px; border-radius:6px; margin:6px 0; }
</style>
</head>
<body>
<h1>{name}</h1>
<p>Este addon consulta <strong>7 fuentes en paralelo</strong>, devuelve solo castellano espanol
y <strong style="color:#7fe3a8">exclusivamente enlaces directos YA CACHEADOS en AllDebrid</strong>.
No se devuelve ningun magnet ni enlace P2P: si un torrent no esta en la cache de AllDebrid, se descarta.
TorrentClaw y Comet solo se aceptan en modo INSTANT/[AD⚡]; DeepFlix, Meteor, TorrentsDB y AnimES quedan fuera.</p>

<h2>Fuentes activas</h2>
{sources}

<h2>1. Clave de AllDebrid (OBLIGATORIA)</h2>
<p>La encuentras en <a href="https://alldebrid.com/apikeys/" target="_blank" style="color:#23CC98">alldebrid.com/apikeys</a>.
Se valida contra la API v4. Sin clave no hay enlaces cacheados, por eso el addon no devolvera ningun stream.</p>
<input type="text" id="apikey" placeholder="Pega aqui tu API key de AllDebrid" autocomplete="off">

<h2>2. Fuentes a usar</h2>
{checks}

<button onclick="guardar()">Validar y generar URL de instalacion</button>
<div id="msg"></div>
<div id="result" style="display:none; margin-top:20px;">
  <p><strong>URL para instalar en Nuvio:</strong></p>
  <code id="installurl"></code>
  <p style="margin-top:10px"><a id="installlink" href="#" style="color:#23CC98">Instalar addon</a></p>
</div>

<script>
async function guardar() {
  const key = document.getElementById('apikey').value.trim();
  const sources = Array.from(document.querySelectorAll('input[name=src]:checked')).map(e => e.value);
  const msg = document.getElementById('msg');
  msg.style.display = 'block';
  if (sources.length === 0) { msg.className='err'; msg.textContent='Selecciona al menos una fuente.'; return; }
  if (!key) { msg.className='err'; msg.textContent='La clave de AllDebrid es obligatoria (solo se sirven enlaces cacheados).'; return; }
  msg.className=''; msg.textContent='Validando...';

  const cfg = { alldebrid: key, sources: sources };
  try {
    const resp = await fetch('/configure?make=' + encodeURIComponent(JSON.stringify(cfg)) + '&validate=1');
    const data = await resp.json();
    if (data.valid) {
      msg.className='ok'; msg.textContent = data.message || 'Configuracion lista';
      document.getElementById('installurl').textContent = data.installUrl;
      document.getElementById('installlink').href = data.installUrl;
      document.getElementById('result').style.display='block';
    } else {
      msg.className='err'; msg.textContent = data.message || 'Error';
      document.getElementById('result').style.display='none';
    }
  } catch(e) {
    msg.className='err'; msg.textContent='Error de conexion con el addon: ' + e.message;
  }
}
</script>
</body>
</html>
"""

_sources_html = "".join(
    f"<div class='src'><strong>{v['label']}</strong></div>" for v in SOURCES.values()
)
_checks_html = "".join(
    f"<label><input type='checkbox' name='src' value='{k}' checked> {v['label']}</label>"
    for k, v in SOURCES.items()
)
CONFIGURE_HTML = (
    CONFIGURE_HTML
    .replace("{name}", ADDON_NAME)
    .replace("{sources}", _sources_html)
    .replace("{checks}", _checks_html)
)


# =====================================================
# SERVIDOR HTTP
# =====================================================

class NuvioAddonHandler(BaseHTTPRequestHandler):
    def log_message(self, fmt: str, *args: Any) -> None:
        print(f"[HTTP] {self.address_string()} - {fmt % args}")

    def _send(self, body: bytes, content_type: str, status: int = 200, cache: bool = True) -> None:
        self.send_response(status)
        self.send_header("Content-Type", content_type)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Access-Control-Allow-Methods", "GET, OPTIONS")
        self.send_header("Access-Control-Allow-Headers", "Content-Type")
        self.send_header("Cache-Control", "public, max-age=300" if cache else "no-store")
        self.end_headers()
        self.wfile.write(body)

    def _send_json(self, data: Any, status: int = 200, cache: bool = True) -> None:
        self._send(
            json.dumps(data, ensure_ascii=False).encode("utf-8"),
            "application/json; charset=utf-8", status, cache,
        )

    def _send_html(self, html: str) -> None:
        self._send(html.encode("utf-8"), "text/html; charset=utf-8", cache=False)

    def _extract_config(self, path: str, query: Dict[str, List[str]]) -> Dict[str, Any]:
        if query.get("config"):
            return decode_config(query["config"][0])
        if query.get("alldebrid"):
            return {"alldebrid": query["alldebrid"][0]}
        segments = [s for s in path.split("/") if s]
        if segments:
            cfg = decode_config(segments[0])
            if cfg:
                return cfg
        return {}

    def _install_url(self, cfg: Dict[str, Any]) -> str:
        """URL instalable: siempre HTTPS publica y terminada en /manifest.json.

        En local se respeta el Host (http://localhost:puerto). En hosting no se
        usa el header Host: Beamup/Render lo reescriben a un nombre interno que
        el cliente (Nuvio) no puede resolver ("host desconocido").
        """
        host = (self.headers.get("Host") or "").strip()
        if host.startswith(("localhost", "127.0.0.1")):
            base = f"http://{host}"
        else:
            base = PUBLIC_ADDON_URL
        return f"{base}/{encode_config(cfg)}/manifest.json"

    def do_OPTIONS(self) -> None:
        self.send_response(204)
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Access-Control-Allow-Methods", "GET, OPTIONS")
        self.send_header("Access-Control-Allow-Headers", "Content-Type")
        self.end_headers()

    def do_GET(self) -> None:
        parsed = urllib.parse.urlparse(self.path)
        path = parsed.path
        query = urllib.parse.parse_qs(parsed.query)

        # --- Configuracion: generar URL / validar clave ---
        if path == "/configure" and "make" in query:
            try:
                cfg = json.loads(query["make"][0])
            except Exception:
                cfg = {}
            key = (cfg.get("alldebrid") or "").strip()
            message = "Configuracion lista"
            valid = True
            if query.get("validate") and key:
                valid, message = validate_alldebrid_key(key)
            install_url = ""
            if valid:
                clean = {
                    "alldebrid": key,
                    "sources": [s for s in cfg.get("sources", []) if s in SOURCES] or DEFAULT_SOURCES,
                }
                install_url = self._install_url(clean)
            self._send_json({
                "valid": valid, "message": message, "installUrl": install_url,
            }, cache=False)
            return

        if path == "/configure":
            self._send_html(CONFIGURE_HTML)
            return

        # --- Health ---
        if path in ("/", "/health"):
            self._send_json({
                "status": "ok", "addon": ADDON_NAME, "version": ADDON_VERSION,
                "configure": "/configure", "sources": list(SOURCES.keys()),
            })
            return

        # --- Config y manifiesto ---
        cfg = self._extract_config(path, query)
        alldebrid_key = (cfg.get("alldebrid") or "").strip()
        enabled = [s for s in cfg.get("sources", []) if s in SOURCES] or DEFAULT_SOURCES

        if path.endswith("/manifest.json") or path == "/manifest.json":
            self._send_json(build_manifest())
            return

        # Algunos clientes piden el manifiesto a la URL base del config, sin
        # /manifest.json. Aceptamos /{config} y /{config}/ por compatibilidad.
        if re.fullmatch(r"/[^/]+/?", path) and decode_config(path.strip("/")):
            self._send_json(build_manifest())
            return

        # --- Streams ---
        m = re.match(r"^(?:/[^/]+)?/stream/(movie|series)/([^/]+?)\.json$", path)
        if m:
            media_type, raw_id = m.group(1), m.group(2)
            # Nuvio/Stremio envian los dos puntos de series codificados (%3A).
            # Sin decodificar, las fuentes reciben un ID invalido y devuelven 0.
            raw_id = urllib.parse.unquote(raw_id)
            print(f"[INFO] Stream {media_type} {raw_id} | fuentes={enabled}")
            streams = build_streams(media_type, raw_id, alldebrid_key, enabled)
            self._send_json({"streams": streams})
            return

        self._send_json({"error": "Not found", "path": path}, status=404)


def run_server(host: str = HOST, port: int = PORT) -> None:
    server = ThreadingHTTPServer((host, port), NuvioAddonHandler)
    print("=" * 68)
    print(f"  {ADDON_NAME} v{ADDON_VERSION}")
    print("=" * 68)
    print(f"  Servidor:   http://localhost:{port}")
    print(f"  Configurar: http://localhost:{port}/configure")
    print(f"  Health:     http://localhost:{port}/health")
    print("  Fuentes:    " + ", ".join(SOURCES.keys()))
    print("=" * 68)
    print("  1. Abrir /configure, pegar la API key de AllDebrid")
    print("  2. Copiar la URL generada")
    print("  3. Nuvio -> Administrar Addons -> Instalar desde URL")
    print("=" * 68)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\n[*] Deteniendo servidor...")
        server.shutdown()


if __name__ == "__main__":
    import sys
    # En hosting (Beamup/Render/Heroku) el puerto llega en la variable PORT
    try:
        port = int(os.environ.get("PORT", PORT))
    except ValueError:
        port = PORT
    if len(sys.argv) > 1:
        try:
            port = int(sys.argv[1])
        except ValueError:
            print(f"Puerto invalido: {sys.argv[1]}")
            sys.exit(1)
    run_server(port=port)
