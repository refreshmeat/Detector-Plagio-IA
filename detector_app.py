from __future__ import annotations

import base64
import io
import json
import math
import os
import re
import statistics
import sys
import threading
import time
import urllib.parse
import unicodedata
import zipfile
from dataclasses import dataclass
from datetime import datetime
from difflib import SequenceMatcher
from pathlib import Path
from xml.etree import ElementTree as ET

import requests
import tkinter as tk
from bs4 import BeautifulSoup
from tkinter import ttk, filedialog, messagebox

from pypdf import PdfReader
from reportlab.lib import colors
from reportlab.lib.pagesizes import A4
from reportlab.lib.styles import ParagraphStyle, getSampleStyleSheet
from reportlab.lib.units import cm
from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, Table, TableStyle, PageBreak, KeepTogether, HRFlowable

APP_NAME = "Detector Plagio IA"
APP_DIR = Path(os.environ.get("LOCALAPPDATA", str(Path.home()))) / "DetectorPlagioIA"
APP_DIR.mkdir(parents=True, exist_ok=True)
CALIBRATION_FILE = APP_DIR / "calibration.json"
SCRIPT_DIR = Path(__file__).resolve().parent
AI_MODEL_FILE = SCRIPT_DIR / "ai_detector_model.joblib"
AI_META_FILE = SCRIPT_DIR / "ai_detector_meta.json"

SUPPORTED = {".pdf", ".docx", ".txt", ".md"}
USER_AGENT = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 Chrome/153 Safari/537.36"
MODEL_OBSERVER = "TucanoBR/Tucano-1b1"
MODEL_PERFORMER = "TucanoBR/Tucano-1b1-Instruct"
MODEL_MAX_TOKENS = 192
AI_BLOCK_WORDS = 150
AI_MAX_BLOCKS = 24

STOPWORDS = {
    "a","o","as","os","um","uma","uns","umas","de","do","da","dos","das","em","no","na","nos","nas",
    "para","por","com","sem","sob","sobre","e","ou","mas","que","se","ao","aos","à","às","como","mais",
    "menos","muito","muita","muitos","muitas","seu","sua","seus","suas","este","esta","estes","estas",
    "esse","essa","esses","essas","isso","isto","aquele","aquela","aqueles","aquelas","ser","estar","ter",
    "foi","foram","são","é","era","eram","pelo","pela","pelos","pelas","também","ainda","já","entre"
}

@dataclass
class WebMatch:
    excerpt: str
    title: str
    url: str
    similarity: float
    evidence: str

def clean_text(text: str) -> str:
    text = (text or "").replace("\x00", " ")
    text = re.sub(r"\r\n?", "\n", text)
    text = re.sub(r"[ \t]+", " ", text)
    text = re.sub(r"\n{3,}", "\n\n", text)
    return text.strip()

def normalize(text: str) -> str:
    text = (text or "").lower()
    text = re.sub(r"[^\w\sáàâãéèêíïóôõöúçñ-]", " ", text, flags=re.UNICODE)
    return re.sub(r"\s+", " ", text).strip()

def word_tokens(text: str) -> list[str]:
    return re.findall(r"\b[\wÀ-ÿ'-]+\b", (text or "").lower(), flags=re.UNICODE)

def read_docx(path: Path) -> str:
    with zipfile.ZipFile(path) as z:
        xml = z.read("word/document.xml")
    root = ET.fromstring(xml)
    ns = "{http://schemas.openxmlformats.org/wordprocessingml/2006/main}"
    paras = []
    for p in root.iter(ns + "p"):
        bits = [node.text or "" for node in p.iter(ns + "t")]
        if bits:
            paras.append("".join(bits))
    return clean_text("\n".join(paras))

def extract_text(path: Path) -> str:
    suffix = path.suffix.lower()
    if suffix == ".pdf":
        reader = PdfReader(str(path))
        return clean_text("\n".join((p.extract_text() or "") for p in reader.pages))
    if suffix == ".docx":
        return read_docx(path)
    if suffix in {".txt", ".md"}:
        data = path.read_bytes()
        for enc in ("utf-8", "utf-8-sig", "latin-1"):
            try:
                return clean_text(data.decode(enc))
            except UnicodeDecodeError:
                continue
        return clean_text(data.decode("utf-8", errors="ignore"))
    raise ValueError(f"Formato não suportado: {suffix}")

def split_sentences(text: str) -> list[str]:
    parts = re.split(r"(?<=[.!?])\s+|\n+", clean_text(text))
    return [p.strip() for p in parts if len(word_tokens(p)) >= 9]

CITATION_END_RE = re.compile(
    r"(?:\(|\b)(?:[A-ZÁÀÂÃÉÊÍÓÔÕÚÇ][A-ZÁÀÂÃÉÊÍÓÔÕÚÇ\-]+(?:\s+E\s+[A-ZÁÀÂÃÉÊÍÓÔÕÚÇ][A-ZÁÀÂÃÉÊÍÓÔÕÚÇ\-]+)?"
    r"|[A-ZÁÀÂÃÉÊÍÓÔÕÚÇ][a-záàâãéêíóôõúç\-]+)"
    r"(?:\s*(?:,|et\s+al\.?))?\s*\(?\s*\d{4}[a-z]?"
    r"(?:\s*,?\s*p{1,2}\.?\s*\d+(?:[-–]\d+)?)?\s*\)?[.!;:]?\s*$",
    flags=re.UNICODE
)

def _citation_near(text: str, start: int, end: int) -> bool:
    window = text[max(0, start-180):min(len(text), end+220)]
    patterns = [
        r"\(\s*[A-ZÁÀÂÃÉÊÍÓÔÕÚÇ][A-Za-zÁÀÂÃÉÊÍÓÔÕÚÇáàâãéêíóôõúç' -]{1,60},?\s*(?:et\s+al\.?\s*)?,?\s*(?:19|20)\d{2}[a-z]?(?:\s*,\s*p{1,2}\.?\s*\d+(?:[-–]\d+)?)?\s*\)",
        r"[A-ZÁÀÂÃÉÊÍÓÔÕÚÇ][A-Za-zÁÀÂÃÉÊÍÓÔÕÚÇáàâãéêíóôõúç' -]{1,60}\s*\(\s*(?:19|20)\d{2}[a-z]?(?:\s*,\s*p{1,2}\.?\s*\d+(?:[-–]\d+)?)?\s*\)",
        r"\[\s*\d{1,3}\s*\]",
    ]
    return any(re.search(pat, window, flags=re.IGNORECASE) for pat in patterns)

def _looks_like_direct_citation_paragraph(paragraph: str) -> bool:
    p = paragraph.strip()
    if len(word_tokens(p)) < 18:
        return False
    # ABNT author-date-page at the end of a long paragraph is a strong signal of direct quotation.
    if re.search(r"\(\s*[A-ZÁÀÂÃÉÊÍÓÔÕÚÇ][A-ZÁÀÂÃÉÊÍÓÔÕÚÇ\-\s]+,\s*\d{4}[a-z]?\s*,\s*p{1,2}\.?\s*\d+(?:[-–]\d+)?\s*\)\s*[.!;:]?$", p):
        return True
    # Narrative citation with page near the end, e.g. Silva (2020, p. 15).
    if re.search(r"[A-ZÁÀÂÃÉÊÍÓÔÕÚÇ][a-záàâãéêíóôõúç\-]+\s*\(\s*\d{4}[a-z]?\s*,\s*p{1,2}\.?\s*\d+(?:[-–]\d+)?\s*\)\s*[.!;:]?$", p):
        return True
    return False

def prepare_plagiarism_text(text: str) -> tuple[str, dict]:
    original = clean_text(text)
    excluded = []
    work = original

    # References section is not plagiarism evidence.
    ref_match = re.search(r"(?im)^\s*(REFERÊNCIAS|REFERENCIAS|REFERENCES)\s*$", work)
    references_removed = 0
    if ref_match:
        refs = work[ref_match.start():].strip()
        references_removed = len(word_tokens(refs))
        if refs:
            excluded.append(("Seção de referências", refs[:600]))
        work = work[:ref_match.start()].rstrip()

    # Text between quotation marks is excluded only when a bibliographic citation is nearby.
    # Quotation marks alone do not make copied text legitimate.
    quote_patterns = [
        r'“[^”]{20,}”',
        r'\"[^\"\n]{20,}\"',
        r'«[^»]{20,}»',
    ]
    quoted_words = 0
    for pat in quote_patterns:
        def repl(m):
            nonlocal quoted_words
            txt = m.group(0)
            if _citation_near(work, m.start(), m.end()):
                quoted_words += len(word_tokens(txt))
                excluded.append(("Citação direta identificada e referenciada", txt[:600]))
                return " "
            return txt
        work = re.sub(pat, repl, work, flags=re.DOTALL)

    # Long direct quotations often lose indentation when extracted from PDF/DOCX.
    # When a long paragraph ends in author-year-page, exclude that paragraph.
    kept_paras = []
    block_words = 0
    for para in re.split(r"\n\s*\n|\n", work):
        ptxt = para.strip()
        if not ptxt:
            continue
        if _looks_like_direct_citation_paragraph(ptxt):
            block_words += len(word_tokens(ptxt))
            excluded.append(("Citação direta longa identificada por autor/ano/página", ptxt[:600]))
            continue
        kept_paras.append(ptxt)

    cleaned = clean_text("\n".join(kept_paras))
    return cleaned, {
        "excluded_items": excluded[:50],
        "quoted_words": quoted_words,
        "direct_block_words": block_words,
        "reference_words": references_removed,
        "excluded_words_total": quoted_words + block_words + references_removed,
        "original_words": len(word_tokens(original)),
        "analyzed_words": len(word_tokens(cleaned)),
    }

def make_search_chunks(text: str, max_chunks: int) -> list[str]:
    """
    Build substantial, non-overlapping windows. Plagiarism should be confirmed on
    passages, not on isolated generic sentences.
    """
    ws = word_tokens(text)
    if len(ws) < 55:
        return [" ".join(ws)] if len(ws) >= 35 else []
    window = 90
    candidates = []
    for i in range(0, len(ws), window):
        part = ws[i:i+window]
        if len(part) >= 55:
            candidates.append(" ".join(part))
    if not candidates:
        return []
    if len(candidates) <= max_chunks:
        return candidates
    idxs = sorted(set(round(i * (len(candidates)-1) / (max_chunks-1)) for i in range(max_chunks)))
    return [candidates[i] for i in idxs]


def decode_bing_url(url: str) -> str:
    try:
        parsed = urllib.parse.urlparse(url)
        if "bing.com/ck/a" not in url:
            return url
        qs = urllib.parse.parse_qs(parsed.query)
        u = qs.get("u", [""])[0]
        if u.startswith("a1"):
            raw = u[2:]
            raw += "=" * (-len(raw) % 4)
            decoded = base64.urlsafe_b64decode(raw).decode("utf-8", errors="ignore")
            if decoded.startswith("http"):
                return decoded
    except Exception:
        pass
    return url

def bing_search(query: str, limit: int = 5) -> list[dict]:
    r = requests.get(
        "https://www.bing.com/search",
        params={"q": query, "count": max(5, limit), "setlang": "pt-br"},
        headers={"User-Agent": USER_AGENT},
        timeout=15,
    )
    if r.status_code != 200:
        raise RuntimeError(f"Busca web indisponível (HTTP {r.status_code}).")
    soup = BeautifulSoup(r.text, "html.parser")
    out = []
    for item in soup.select("li.b_algo"):
        a = item.select_one("h2 a")
        if not a:
            continue
        title = a.get_text(" ", strip=True)
        href = decode_bing_url(a.get("href", ""))
        p = item.select_one(".b_caption p")
        snippet = p.get_text(" ", strip=True) if p else ""
        if href.startswith("http") and "bing.com/search" not in href:
            out.append({"title": title, "url": href, "snippet": snippet})
        if len(out) >= limit:
            break
    return out

def shingles(text: str, n: int = 5) -> set[tuple[str, ...]]:
    ws = normalize(text).split()
    if len(ws) < n:
        return set()
    return {tuple(ws[i:i+n]) for i in range(len(ws)-n+1)}

def page_text(url: str) -> str:
    try:
        r = requests.get(url, headers={"User-Agent": USER_AGENT}, timeout=12, allow_redirects=True)
        ctype = r.headers.get("content-type", "").lower()
        if r.status_code != 200 or "text/html" not in ctype:
            return ""
        soup = BeautifulSoup(r.text, "html.parser")
        for tag in soup(["script", "style", "noscript", "svg"]):
            tag.decompose()
        return clean_text(soup.get_text(" ", strip=True))[:800000]
    except Exception:
        return ""

def exact_passage_metrics(chunk: str, candidate_text: str) -> dict:
    a = normalize(chunk).split()
    b = normalize(candidate_text).split()
    if not a or not b:
        return {"score":0.0,"longest":0,"substantial":0,"coverage":0.0,"confirmed":False}

    matcher = SequenceMatcher(None, a, b, autojunk=False)
    blocks = [m for m in matcher.get_matching_blocks() if m.size > 0]
    longest = max((m.size for m in blocks), default=0)
    substantial = sum(m.size for m in blocks if m.size >= 10)
    coverage = substantial / max(1, len(a))

    # A single generic phrase must never become plagiarism. Require a long verbatim
    # run, or multiple sizeable runs covering a large share of the sampled passage.
    confirmed = (
        longest >= 28
        or (longest >= 18 and substantial >= 45 and coverage >= 0.45)
    )
    score = 100.0 * coverage if confirmed else 0.0
    return {
        "score": min(100.0, score),
        "longest": int(longest),
        "substantial": int(substantial),
        "coverage": float(coverage),
        "confirmed": bool(confirmed),
    }

def chunk_similarity(chunk: str, candidate_text: str) -> float:
    return exact_passage_metrics(chunk, candidate_text)["score"]


def build_queries(chunk: str) -> list[str]:
    raw = normalize(chunk)
    words = raw.split()
    content = [w for w in words if len(w) > 3 and w not in STOPWORDS]
    queries = []
    if len(words) >= 8:
        queries.append('"' + " ".join(words[:8]) + '"')
    if content:
        queries.append(" ".join(content[:12]))
        if len(content) > 8:
            queries.append(" ".join(content[:5] + content[-5:]))
    if not queries:
        queries.append(" ".join(words[:12]))
    out=[]
    seen=set()
    for q in queries:
        q=q.strip()
        if q and q not in seen:
            seen.add(q); out.append(q)
    return out[:3]

def wikipedia_search(query: str, limit: int = 5) -> list[dict]:
    try:
        api = "https://pt.wikipedia.org/w/api.php"
        r = requests.get(
            api,
            params={"action":"query","list":"search","srsearch":query.strip('"'),"utf8":1,"format":"json","srlimit":max(1,min(limit,10))},
            headers={"User-Agent":USER_AGENT},
            timeout=15,
        )
        if r.status_code != 200:
            return []
        hits=r.json().get("query",{}).get("search",[])
        if not hits:
            return []
        pageids="|".join(str(x["pageid"]) for x in hits)
        r2=requests.get(
            api,
            params={"action":"query","prop":"extracts|info","pageids":pageids,"explaintext":1,"inprop":"url","format":"json","exsectionformat":"plain"},
            headers={"User-Agent":USER_AGENT},
            timeout=15,
        )
        if r2.status_code != 200:
            return []
        pages=r2.json().get("query",{}).get("pages",{})
        out=[]
        for hit in hits:
            pg=pages.get(str(hit["pageid"]),{})
            title=pg.get("title") or hit.get("title") or ""
            url=pg.get("fullurl") or f"https://pt.wikipedia.org/?curid={hit['pageid']}"
            extract=clean_text(pg.get("extract",""))
            out.append({"title":title,"url":url,"snippet":extract[:12000],"backend":"Wikipedia"})
        return out
    except Exception:
        return []

def openalex_search(query: str, limit: int = 5) -> list[dict]:
    try:
        r = requests.get(
            "https://api.openalex.org/works",
            params={"search": query.strip('"'), "per-page": max(1, min(limit, 10)), "select": "id,display_name,doi,primary_location,abstract_inverted_index"},
            headers={"User-Agent": USER_AGENT},
            timeout=15,
        )
        if r.status_code != 200:
            return []
        out=[]
        for w in r.json().get("results",[]):
            title=w.get("display_name") or ""
            loc=w.get("primary_location") or {}
            url=w.get("doi") or loc.get("landing_page_url") or w.get("id") or ""
            inv=w.get("abstract_inverted_index") or {}
            abstract=""
            if inv:
                pairs=[]
                for token,poses in inv.items():
                    for pos in poses:
                        pairs.append((pos,token))
                pairs.sort()
                abstract=" ".join(tok for _,tok in pairs)
            if url:
                out.append({"title":title,"url":url,"snippet":abstract[:5000],"backend":"OpenAlex"})
        return out
    except Exception:
        return []

def web_candidates(chunk: str, depth: str) -> list[dict]:
    found=[]
    seen=set()
    for q in build_queries(chunk):
        try:
            for item in bing_search(q, 7 if depth=="Profunda" else 5):
                key=item.get("url","")
                if key and key not in seen:
                    seen.add(key); item["backend"]="Bing"; found.append(item)
        except Exception:
            pass
    # Academic fallback/parallel index. Particularly useful for TCCs, theses and papers.
    academic_query=" ".join([w for w in normalize(chunk).split() if len(w)>3 and w not in STOPWORDS][:16])
    for item in openalex_search(academic_query, 7 if depth=="Profunda" else 5):
        key=item.get("url","")
        if key and key not in seen:
            seen.add(key); found.append(item)
    # Stable public encyclopedia index catches copied definitions that generic search engines often mangle in PT-BR.
    wiki_query=" ".join(normalize(chunk).split()[:14])
    for item in wikipedia_search(wiki_query, 5):
        key=item.get("url","")
        if key and key not in seen:
            seen.add(key); found.append(item)
    return found[:30]



def internet_similarity(text: str, depth: str, status_cb=None) -> dict:
    plagiarism_text, exclusions = prepare_plagiarism_text(text)
    max_chunks = {"Rápida": 8, "Normal": 16, "Profunda": 28}.get(depth, 16)
    chunks = make_search_chunks(plagiarism_text, max_chunks)
    if not chunks:
        return {"percentage": 0.0, "matches": [], "checked": 0, "total": 0, "status": "Texto insuficiente após descontar citações/referências.", "exclusions": exclusions}

    matches: list[WebMatch] = []
    scores = []
    search_failures = 0

    for i, chunk in enumerate(chunks, 1):
        if status_cb:
            status_cb(f"Antiplágio web: trecho {i}/{len(chunks)}")
        try:
            results = web_candidates(chunk, depth)
            if not results:
                raise RuntimeError("Nenhum backend retornou candidatos.")
        except Exception:
            search_failures += 1
            scores.append(0.0)
            continue

        best_score = 0.0
        best_match = None
        chunk_content = {w for w in normalize(chunk).split() if len(w) > 3 and w not in STOPWORDS}
        for result in results:
            # OpenAlex/Wikipedia already return substantial indexed text. Bing snippets are
            # discovery hints only; fetch the page only when there is enough lexical overlap
            # to justify the network request.
            snippet = result.get("snippet","") or ""
            backend = result.get("backend","Web")
            candidate_text = snippet
            if backend == "Bing":
                sw = {w for w in normalize(result.get("title","") + " " + snippet).split()
                      if len(w) > 3 and w not in STOPWORDS}
                lexical = len(chunk_content & sw) / max(1, len(chunk_content))
                if lexical < 0.22:
                    continue
                body = page_text(result["url"])
                if not body:
                    continue
                candidate_text = body
            metrics = exact_passage_metrics(chunk, candidate_text)
            score = metrics["score"]
            if not metrics["confirmed"]:
                continue
            evidence = (
                f"Correspondência literal confirmada: maior sequência contínua de "
                f"{metrics['longest']} palavras; {metrics['substantial']} palavras "
                f"em segmentos substanciais ({metrics['coverage']*100:.1f}% do trecho amostrado)."
            )
            if score > best_score:
                best_score = score
                best_match = WebMatch(
                    excerpt=chunk,
                    title=result["title"],
                    url=result["url"],
                    similarity=score,
                    evidence=(f"[{result.get('backend','Web')}] " + evidence)[:500],
                )
        scores.append(best_score)
        if best_match and best_score >= 35:
            matches.append(best_match)
        time.sleep(0.25)

    if search_failures == len(chunks):
        raise RuntimeError("O mecanismo gratuito de busca bloqueou ou não respondeu. Nenhuma porcentagem foi inventada.")

    percentage = sum(min(100.0, s) for s in scores) / len(scores)
    status = f"Estimativa por amostragem de {len(chunks)} trechos longos distribuídos pelo documento. Só são contabilizadas correspondências literais substanciais confirmadas na fonte."
    if search_failures:
        status += f" {search_failures} consulta(s) falharam."
    by_url = {}
    for m in matches:
        prev = by_url.get(m.url)
        if prev is None or m.similarity > prev.similarity:
            by_url[m.url] = m
    unique_matches = sorted(by_url.values(), key=lambda m: m.similarity, reverse=True)[:30]
    return {
        "percentage": round(percentage, 1),
        "matches": unique_matches,
        "checked": len(chunks) - search_failures,
        "total": len(chunks),
        "status": status,
        "exclusions": exclusions,
    }

def make_ai_blocks(text: str, block_words: int = 150, max_blocks: int = 30) -> tuple[list[str], bool]:
    ws = word_tokens(text)
    if len(ws) < 90:
        return [], False
    blocks = []
    # Non-overlapping blocks avoid counting the same words twice in the final percentage.
    for i in range(0, len(ws), block_words):
        b = ws[i:i+block_words]
        if len(b) >= 80:
            blocks.append(" ".join(b))
    sampled = False
    if len(blocks) > max_blocks:
        sampled = True
        idxs = sorted(set(round(i * (len(blocks)-1) / (max_blocks-1)) for i in range(max_blocks)))
        blocks = [blocks[i] for i in idxs]
    return blocks, sampled

_AI_BUNDLE = None
_AI_META = None

def load_ai_classifier():
    global _AI_BUNDLE, _AI_META
    if _AI_BUNDLE is None:
        if not AI_MODEL_FILE.exists():
            raise RuntimeError("Modelo local de IA não encontrado.")
        import joblib
        _AI_BUNDLE = joblib.load(AI_MODEL_FILE)
    if _AI_META is None:
        try:
            _AI_META = json.loads(AI_META_FILE.read_text(encoding="utf-8"))
        except Exception:
            _AI_META = {}
    return _AI_BUNDLE, _AI_META

def ai_analysis(text: str, status_cb=None) -> dict:
    blocks, sampled = make_ai_blocks(text)
    if not blocks:
        return {
            "percentage": None,
            "classification": "Inconclusivo",
            "reason": "Texto autoral curto demais para análise confiável.",
            "blocks": [],
            "sampled": False,
            "calibration": {},
        }

    if status_cb:
        status_cb("Carregando classificador PT-BR de IA...")
    bundle, meta = load_ai_classifier()
    features = bundle["features"]
    clf = bundle["classifier"]

    moderate_threshold = float(
        meta.get("moderate_threshold",
                 bundle.get("threshold", meta.get("threshold", 0.85)))
    )
    strong_threshold = float(
        meta.get("strong_threshold",
                 max(0.90, moderate_threshold + 0.05))
    )

    if status_cb:
        status_cb(f"Detecção de IA: analisando {len(blocks)} bloco(s)...")
    X = features.transform(blocks)
    probs = clf.predict_proba(X)[:,1].tolist()

    raw_rows=[]
    for i,(block,prob) in enumerate(zip(blocks,probs),1):
        wc=len(word_tokens(block))
        raw_rows.append({
            "index":i,
            "score":float(prob),
            "words":wc,
            "excerpt":block[:360],
            "moderate": bool(prob >= moderate_threshold),
            "strong_raw": bool(prob >= strong_threshold),
        })

    # A strong headline signal must be sustained. One isolated strong block in a
    # document with several blocks is reported for review, but does not turn its
    # entire word count into "AI".
    strong_idxs=[i for i,r in enumerate(raw_rows) if r["strong_raw"]]
    sustained=set()
    if len(raw_rows) == 1:
        # Very short texts need exceptionally strong evidence.
        if raw_rows[0]["score"] >= max(0.97, strong_threshold):
            sustained.add(0)
    elif len(strong_idxs) >= 2:
        # Count strong blocks only when there is corroboration elsewhere.
        sustained.update(strong_idxs)

    rows=[]
    strong_words=0
    moderate_words=0
    isolated_words=0
    total_words=sum(r["words"] for r in raw_rows)

    for i,r in enumerate(raw_rows):
        flagged = i in sustained
        isolated = r["strong_raw"] and not flagged
        uncertain = r["moderate"] and not r["strong_raw"]
        if flagged:
            strong_words += r["words"]
        elif isolated:
            isolated_words += r["words"]
        elif uncertain:
            moderate_words += r["words"]
        rows.append({
            "index":r["index"],
            "score":r["score"],
            "flagged":flagged,
            "isolated_strong":isolated,
            "uncertain":uncertain,
            "words":r["words"],
            "excerpt":r["excerpt"],
        })

    percentage = 100.0 * strong_words / max(1,total_words)
    moderate_pct = 100.0 * moderate_words / max(1,total_words)
    isolated_pct = 100.0 * isolated_words / max(1,total_words)

    if percentage == 0:
        cls="Sem sinal forte sustentado"
    elif percentage < 25:
        cls="Sinal forte localizado"
    elif percentage < 60:
        cls="Sinal forte em parte relevante"
    else:
        cls="Sinal forte extenso"

    return {
        "percentage": round(percentage,1),
        "uncertain_percentage": round(moderate_pct,1),
        "isolated_strong_percentage": round(isolated_pct,1),
        "classification": cls,
        "reason": (
            "O percentual principal conta apenas palavras em blocos com sinal estatístico forte "
            "e sustentado por mais de um bloco. Sinais moderados ou fortes isolados são mostrados "
            "para revisão, mas não são tratados como prova de geração por IA."
        ),
        "blocks": rows,
        "sampled": sampled,
        "calibration": meta,
        "threshold": moderate_threshold,
        "strong_threshold": strong_threshold,
        "mean_score": round(sum(probs)/len(probs),4),
        "analyzed_words": total_words,
        "analyzed_blocks": len(blocks),
    }



def esc(s) -> str:
    return str(s).replace("&","&amp;").replace("<","&lt;").replace(">","&gt;")

def make_report_pdf(path: Path, name: str, web: dict, ai: dict, words_count: int):
    styles = getSampleStyleSheet()
    navy = colors.HexColor("#203047")
    blue = colors.HexColor("#315EFB")
    green = colors.HexColor("#178C65")
    amber = colors.HexColor("#B56C00")
    red = colors.HexColor("#B23A48")
    ink = colors.HexColor("#243041")
    muted = colors.HexColor("#667085")
    line = colors.HexColor("#D8DEE8")
    soft = colors.HexColor("#F5F7FA")
    white = colors.white

    styles.add(ParagraphStyle(
        name="ReportTitle", parent=styles["Title"], fontName="Helvetica-Bold",
        fontSize=20, leading=24, textColor=white, spaceAfter=4
    ))
    styles.add(ParagraphStyle(
        name="ReportSubtitle", parent=styles["BodyText"], fontName="Helvetica",
        fontSize=9.5, leading=13, textColor=colors.HexColor("#DDE5F0")
    ))
    styles.add(ParagraphStyle(
        name="SectionTitleX", parent=styles["Heading2"], fontName="Helvetica-Bold",
        fontSize=13.5, leading=17, textColor=navy, spaceBefore=4, spaceAfter=8
    ))
    styles.add(ParagraphStyle(
        name="BodyX", parent=styles["BodyText"], fontName="Helvetica",
        fontSize=9.2, leading=13.2, textColor=ink, spaceAfter=7
    ))
    styles.add(ParagraphStyle(
        name="SmallX", parent=styles["BodyText"], fontName="Helvetica",
        fontSize=8.1, leading=11.2, textColor=muted, spaceAfter=4
    ))
    styles.add(ParagraphStyle(
        name="CardNumber", parent=styles["Heading1"], fontName="Helvetica-Bold",
        fontSize=22, leading=24, textColor=navy, alignment=1, spaceAfter=2
    ))
    styles.add(ParagraphStyle(
        name="CardLabel", parent=styles["BodyText"], fontName="Helvetica-Bold",
        fontSize=8.6, leading=10.5, textColor=muted, alignment=1
    ))
    styles.add(ParagraphStyle(
        name="SourceTitle", parent=styles["BodyText"], fontName="Helvetica-Bold",
        fontSize=9.2, leading=12, textColor=navy, spaceAfter=3
    ))
    styles.add(ParagraphStyle(
        name="SourceText", parent=styles["BodyText"], fontName="Helvetica",
        fontSize=7.9, leading=10.8, textColor=ink, spaceAfter=2
    ))

    doc = SimpleDocTemplate(
        str(path), pagesize=A4,
        leftMargin=1.55*cm, rightMargin=1.55*cm,
        topMargin=1.45*cm, bottomMargin=1.35*cm,
        title="Relatório de Similaridade Web e Sinais de IA",
        author="Detector Plagio IA",
    )

    story = []

    header = Table([
        [Paragraph("Relatório de Similaridade Web e Sinais de IA", styles["ReportTitle"])],
        [Paragraph(
            "Análise técnica de similaridade em fontes públicas e de padrões estatísticos compatíveis com texto sintético.",
            styles["ReportSubtitle"]
        )],
    ], colWidths=[17.9*cm])
    header.setStyle(TableStyle([
        ("BACKGROUND",(0,0),(-1,-1),navy),
        ("LEFTPADDING",(0,0),(-1,-1),14),
        ("RIGHTPADDING",(0,0),(-1,-1),14),
        ("TOPPADDING",(0,0),(-1,0),12),
        ("BOTTOMPADDING",(0,1),(-1,1),12),
    ]))
    story += [header, Spacer(1, 10)]

    meta = Table([
        [
            Paragraph(f"<b>Documento</b><br/>{esc(name)}", styles["SmallX"]),
            Paragraph(f"<b>Texto autoral analisado</b><br/>{words_count} palavras", styles["SmallX"]),
            Paragraph(f"<b>Data da análise</b><br/>{datetime.now().strftime('%d/%m/%Y %H:%M')}", styles["SmallX"]),
        ]
    ], colWidths=[7.9*cm, 4.8*cm, 5.2*cm])
    meta.setStyle(TableStyle([
        ("BACKGROUND",(0,0),(-1,-1),soft),
        ("BOX",(0,0),(-1,-1),0.6,line),
        ("INNERGRID",(0,0),(-1,-1),0.4,line),
        ("VALIGN",(0,0),(-1,-1),"TOP"),
        ("LEFTPADDING",(0,0),(-1,-1),9),
        ("RIGHTPADDING",(0,0),(-1,-1),9),
        ("TOPPADDING",(0,0),(-1,-1),8),
        ("BOTTOMPADDING",(0,0),(-1,-1),8),
    ]))
    story += [meta, Spacer(1, 12)]

    web_pct = float(web.get("percentage", 0) or 0)
    ai_pct_val = ai.get("percentage")
    ai_pct = "INCONCLUSIVO" if ai_pct_val is None else f"{float(ai_pct_val):.1f}%"
    web_caption = "Similaridade problemática na web"
    ai_caption = "Sinal forte sustentado de IA"

    summary = Table([
        [
            Paragraph(f"{web_pct:.1f}%", styles["CardNumber"]),
            Paragraph(ai_pct, styles["CardNumber"])
        ],
        [
            Paragraph(web_caption, styles["CardLabel"]),
            Paragraph(ai_caption, styles["CardLabel"])
        ],
    ], colWidths=[8.75*cm, 8.75*cm])
    summary.setStyle(TableStyle([
        ("BACKGROUND",(0,0),(-1,-1),colors.HexColor("#FAFBFC")),
        ("BOX",(0,0),(0,-1),0.8,blue),
        ("BOX",(1,0),(1,-1),0.8,green),
        ("VALIGN",(0,0),(-1,-1),"MIDDLE"),
        ("TOPPADDING",(0,0),(-1,0),12),
        ("BOTTOMPADDING",(0,0),(-1,0),3),
        ("TOPPADDING",(0,1),(-1,1),2),
        ("BOTTOMPADDING",(0,1),(-1,1),11),
    ]))
    story += [summary, Spacer(1, 14)]

    exclusions = web.get("exclusions") or {}
    story += [
        Paragraph("1. Similaridade e antiplágio na internet", styles["SectionTitleX"]),
        Paragraph(
            "O percentual abaixo considera apenas o texto elegível para comparação. Citações diretas devidamente identificadas "
            "e a seção de referências são retiradas do cálculo principal. Uma ocorrência só é contabilizada quando a fonte confirma "
            "um trecho literal substancial: sequência contínua longa ou múltiplos segmentos longos cobrindo parcela relevante do trecho amostrado. "
            "Frases curtas, expressões comuns e mera semelhança temática não entram no percentual. A consulta utiliza índices públicos da web "
            "e de produção acadêmica; conteúdo privado, fechado ou não indexado pode ficar fora da cobertura.",
            styles["BodyX"]
        ),
    ]

    coverage = Table([
        [
            Paragraph("<b>Consultas concluídas</b>", styles["SmallX"]),
            Paragraph(f"{web.get('checked',0)} de {web.get('total',0)}", styles["BodyX"]),
            Paragraph("<b>Palavras excluídas</b>", styles["SmallX"]),
            Paragraph(str(exclusions.get("excluded_words_total",0)), styles["BodyX"]),
        ]
    ], colWidths=[3.2*cm, 2.4*cm, 3.2*cm, 2.4*cm])
    coverage.setStyle(TableStyle([
        ("BACKGROUND",(0,0),(-1,-1),soft),
        ("BOX",(0,0),(-1,-1),0.5,line),
        ("VALIGN",(0,0),(-1,-1),"MIDDLE"),
        ("LEFTPADDING",(0,0),(-1,-1),7),
        ("RIGHTPADDING",(0,0),(-1,-1),7),
        ("TOPPADDING",(0,0),(-1,-1),6),
        ("BOTTOMPADDING",(0,0),(-1,-1),6),
    ]))
    story += [coverage, Spacer(1, 10)]

    matches = web.get("matches", [])
    if matches:
        story.append(Paragraph("Fontes com maior correspondência", styles["BodyX"]))
        for i, m in enumerate(matches[:15], 1):
            sim = float(m.similarity)
            card = Table([
                [
                    Paragraph(f"<b>{i:02d}</b>", styles["SourceTitle"]),
                    Paragraph(f"{sim:.1f}%", styles["SourceTitle"]),
                    Paragraph(esc(m.title), styles["SourceTitle"]),
                ],
                [
                    "",
                    "",
                    Paragraph(f"<b>URL:</b> {esc(m.url)}", styles["SourceText"]),
                ],
                [
                    "",
                    "",
                    Paragraph(f"<b>Evidência:</b> {esc(m.evidence)}", styles["SourceText"]),
                ],
                [
                    "",
                    "",
                    Paragraph(f"<b>Trecho:</b> {esc(m.excerpt)}", styles["SourceText"]),
                ],
            ], colWidths=[0.8*cm, 1.6*cm, 15.1*cm])
            card.setStyle(TableStyle([
                ("BACKGROUND",(0,0),(-1,-1),colors.HexColor("#FBFCFE")),
                ("BOX",(0,0),(-1,-1),0.5,line),
                ("LINEBEFORE",(0,0),(0,-1),3,blue),
                ("VALIGN",(0,0),(-1,-1),"TOP"),
                ("LEFTPADDING",(0,0),(-1,-1),7),
                ("RIGHTPADDING",(0,0),(-1,-1),7),
                ("TOPPADDING",(0,0),(-1,-1),6),
                ("BOTTOMPADDING",(0,0),(-1,-1),5),
                ("SPAN",(0,1),(0,3)),
                ("SPAN",(1,1),(1,3)),
            ]))
            story += [KeepTogether([card, Spacer(1, 6)])]
    else:
        note = Table([[Paragraph(
            "Nenhuma correspondência relevante foi confirmada nas consultas realizadas.",
            styles["BodyX"]
        )]], colWidths=[17.5*cm])
        note.setStyle(TableStyle([
            ("BACKGROUND",(0,0),(-1,-1),soft),
            ("BOX",(0,0),(-1,-1),0.5,line),
            ("LEFTPADDING",(0,0),(-1,-1),10),
            ("RIGHTPADDING",(0,0),(-1,-1),10),
            ("TOPPADDING",(0,0),(-1,-1),9),
            ("BOTTOMPADDING",(0,0),(-1,-1),9),
        ]))
        story += [note]

    story += [PageBreak(), Paragraph("2. Análise de padrões compatíveis com IA", styles["SectionTitleX"])]

    if ai.get("percentage") is None:
        story.append(Paragraph(
            "<b>Resultado inconclusivo.</b> " + esc(ai.get("reason","")),
            styles["BodyX"]
        ))
    else:
        cal = ai.get("calibration") or {}
        fpr = cal.get("test_human_strong_fpr", cal.get("test_human_false_positive_rate"))
        det = cal.get("test_ai_strong_detection", cal.get("test_ai_detection_rate"))
        fpr_txt = "n/d" if fpr is None else f"{100*float(fpr):.2f}%"
        det_txt = "n/d" if det is None else f"{100*float(det):.2f}%"

        method = Table([
            [Paragraph("<b>Limiar moderado</b>", styles["SmallX"]), Paragraph(f"{ai.get('threshold','n/d')}", styles["BodyX"])],
            [Paragraph("<b>Limiar forte</b>", styles["SmallX"]), Paragraph(f"{ai.get('strong_threshold','n/d')}", styles["BodyX"])],
            [Paragraph("<b>Blocos analisados</b>", styles["SmallX"]), Paragraph(str(ai.get("analyzed_blocks",len(ai.get("blocks",[])))), styles["BodyX"])],
            [Paragraph("<b>Palavras elegíveis</b>", styles["SmallX"]), Paragraph(str(ai.get("analyzed_words",words_count)), styles["BodyX"])],
            [Paragraph("<b>Base humana de calibração</b>", styles["SmallX"]), Paragraph(str(cal.get("calibration_human_n","n/d")), styles["BodyX"])],
            [Paragraph("<b>Teste humano independente</b>", styles["SmallX"]), Paragraph(str(cal.get("test_human_n","n/d")), styles["BodyX"])],
            [Paragraph("<b>Falso positivo do sinal forte</b>", styles["SmallX"]), Paragraph(fpr_txt, styles["BodyX"])],
            [Paragraph("<b>Detecção forte de IA no teste</b>", styles["SmallX"]), Paragraph(det_txt, styles["BodyX"])],
        ], colWidths=[6.3*cm, 5.0*cm])
        method.setStyle(TableStyle([
            ("BACKGROUND",(0,0),(-1,-1),soft),
            ("BOX",(0,0),(-1,-1),0.5,line),
            ("INNERGRID",(0,0),(-1,-1),0.35,line),
            ("VALIGN",(0,0),(-1,-1),"MIDDLE"),
            ("LEFTPADDING",(0,0),(-1,-1),8),
            ("RIGHTPADDING",(0,0),(-1,-1),8),
            ("TOPPADDING",(0,0),(-1,-1),5),
            ("BOTTOMPADDING",(0,0),(-1,-1),5),
        ]))
        story += [
            Paragraph(
                f"<b>{float(ai['percentage']):.1f}% do texto elegível apresentou sinal forte sustentado.</b> "
                + esc(ai.get("reason","")),
                styles["BodyX"]
            ),
            Paragraph(
                "<b>Método:</b> classificador local em português brasileiro com vetorização TF-IDF de caracteres e palavras "
                "e regressão logística. O limiar foi definido de forma conservadora para priorizar baixo risco de falso positivo "
                "em texto humano formal.",
                styles["BodyX"]
            ),
            method,
            Spacer(1, 10),
        ]

        if cal.get("calibration_human_n"):
            story.append(Paragraph(
                f"Os limiares foram calibrados em <b>{cal.get('calibration_human_n')} textos humanos</b> separados do treino e "
                f"avaliados novamente em <b>{cal.get('test_human_n','n/d')} textos humanos independentes</b>. "
                "A regra do relatório exige corroboracao entre blocos para que sinal forte entre no percentual principal.",
                styles["BodyX"]
            ))

        warning = Table([[Paragraph(
            "<b>Leitura correta do resultado:</b> o detector identifica padrões estatísticos compatíveis com texto sintético. "
            "Ele não comprova autoria, não distingue com segurança todos os níveis de edição humana e não deve ser usado isoladamente para acusação de uso de IA.",
            styles["BodyX"]
        )]], colWidths=[17.5*cm])
        warning.setStyle(TableStyle([
            ("BACKGROUND",(0,0),(-1,-1),colors.HexColor("#FFF7E8")),
            ("BOX",(0,0),(-1,-1),0.6,amber),
            ("LEFTPADDING",(0,0),(-1,-1),10),
            ("RIGHTPADDING",(0,0),(-1,-1),10),
            ("TOPPADDING",(0,0),(-1,-1),9),
            ("BOTTOMPADDING",(0,0),(-1,-1),9),
        ]))
        story += [warning, Spacer(1, 11), Paragraph("Blocos analisados", styles["BodyX"])]

        block_data = [[
            Paragraph("<b>#</b>", styles["SmallX"]),
            Paragraph("<b>Status</b>", styles["SmallX"]),
            Paragraph("<b>Escore</b>", styles["SmallX"]),
            Paragraph("<b>Trecho</b>", styles["SmallX"]),
        ]]
        for row in ai.get("blocks", [])[:20]:
            if row.get("flagged"):
                status = "Forte sustentado"
                status_color = red
            elif row.get("isolated_strong"):
                status = "Forte isolado"
                status_color = amber
            elif row.get("uncertain"):
                status = "Moderado"
                status_color = amber
            else:
                status = "Sem sinal forte"
                status_color = green
            block_data.append([
                Paragraph(str(row["index"]), styles["SmallX"]),
                Paragraph(f'<font color="{status_color.hexval()}"><b>{status}</b></font>', styles["SmallX"]),
                Paragraph(f"{float(row['score']):.3f}", styles["SmallX"]),
                Paragraph(esc(row["excerpt"]), styles["SmallX"]),
            ])
        bt = Table(block_data, colWidths=[0.7*cm, 2.2*cm, 1.4*cm, 13.2*cm], repeatRows=1)
        bt.setStyle(TableStyle([
            ("BACKGROUND",(0,0),(-1,0),navy),
            ("TEXTCOLOR",(0,0),(-1,0),white),
            ("BOX",(0,0),(-1,-1),0.5,line),
            ("INNERGRID",(0,0),(-1,-1),0.35,line),
            ("VALIGN",(0,0),(-1,-1),"TOP"),
            ("LEFTPADDING",(0,0),(-1,-1),5),
            ("RIGHTPADDING",(0,0),(-1,-1),5),
            ("TOPPADDING",(0,0),(-1,-1),5),
            ("BOTTOMPADDING",(0,0),(-1,-1),5),
        ]))
        story.append(bt)

    story += [
        Spacer(1, 12),
        HRFlowable(width="100%", thickness=0.6, color=line),
        Spacer(1, 5),
        Paragraph(
            "Relatório técnico indicativo. Resultados de similaridade dependem da cobertura dos índices consultados; "
            "resultados de IA são probabilísticos e não constituem prova de autoria.",
            styles["SmallX"]
        )
    ]

    def footer(canvas, docobj):
        canvas.saveState()
        canvas.setStrokeColor(line)
        canvas.setLineWidth(0.4)
        canvas.line(1.55*cm, 0.95*cm, A4[0]-1.55*cm, 0.95*cm)
        canvas.setFillColor(muted)
        canvas.setFont("Helvetica", 7.8)
        canvas.drawString(1.55*cm, 0.65*cm, "Detector Plagio IA - Relatório técnico")
        canvas.drawRightString(A4[0]-1.55*cm, 0.65*cm, f"Página {docobj.page}")
        canvas.restoreState()

    doc.build(story, onFirstPage=footer, onLaterPages=footer)


class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Detector de Plágio e IA")
        self.geometry("1100x800")
        self.minsize(930,650)
        self.target_path = tk.StringVar()
        self.depth = tk.StringVar(value="Normal")
        self.status = tk.StringVar(value="Pronto.")
        self.result = None
        self.build()

    def build(self):
        try:
            ttk.Style(self).theme_use("vista")
        except Exception:
            pass
        root = ttk.Frame(self, padding=14)
        root.pack(fill="both", expand=True)
        ttk.Label(root, text="Detector de Plágio e IA", font=("Segoe UI", 19, "bold")).pack(anchor="w")
        ttk.Label(root, text="Antiplágio na web + detector de IA PT-BR calibrado. PDF e Word também são aceitos.").pack(anchor="w", pady=(0,12))

        box = ttk.LabelFrame(root, text="Entrada", padding=8)
        box.pack(fill="x")
        self.tabs = ttk.Notebook(box)
        self.tabs.pack(fill="x", expand=True)

        paste = ttk.Frame(self.tabs, padding=8)
        filetab = ttk.Frame(self.tabs, padding=8)
        self.tabs.add(paste, text="Colar texto")
        self.tabs.add(filetab, text="PDF / Word")

        self.paste = tk.Text(paste, height=8, wrap="word", font=("Segoe UI",10))
        self.paste.pack(fill="both", expand=True)

        row = ttk.Frame(filetab)
        row.pack(fill="x", pady=8)
        ttk.Entry(row, textvariable=self.target_path).pack(side="left", fill="x", expand=True)
        ttk.Button(row, text="Selecionar PDF/Word", command=self.pick_file).pack(side="left", padx=(8,0))

        opts = ttk.Frame(root)
        opts.pack(fill="x", pady=8)
        ttk.Label(opts, text="Profundidade antiplágio:").pack(side="left")
        ttk.Combobox(opts, textvariable=self.depth, values=["Rápida","Normal","Profunda"], width=12, state="readonly").pack(side="left", padx=6)
        self.analyze_btn = ttk.Button(opts, text="Analisar", command=self.start)
        self.analyze_btn.pack(side="left", padx=(8,0))
        self.pdf_btn = ttk.Button(opts, text="Exportar PDF", command=self.export_pdf, state="disabled")
        self.pdf_btn.pack(side="left", padx=8)
        ttk.Label(opts, textvariable=self.status).pack(side="right")

        self.progress = ttk.Progressbar(root, mode="indeterminate")
        self.progress.pack(fill="x", pady=(0,8))

        ttk.Label(
            root,
            text="O percentual de IA é um indicador calibrado, não uma prova de autoria. O antiplágio cobre somente conteúdo público indexado.",
            foreground="#754C00"
        ).pack(anchor="w", pady=(0,8))

        result_box = ttk.LabelFrame(root, text="Resultado", padding=8)
        result_box.pack(fill="both", expand=True)
        self.result_text = tk.Text(result_box, wrap="word", font=("Segoe UI",10))
        self.result_text.pack(fill="both", expand=True)
        self.result_text.configure(state="disabled")

    def pick_file(self):
        p = filedialog.askopenfilename(filetypes=[("PDF / Word","*.pdf *.docx"),("Documentos","*.pdf *.docx *.txt *.md")])
        if p:
            self.target_path.set(p)
            self.tabs.select(1)

    def set_status_threadsafe(self, msg):
        self.after(0, lambda: self.status.set(msg))

    def get_input(self):
        if self.tabs.index(self.tabs.select()) == 0:
            text = clean_text(self.paste.get("1.0","end"))
            return text, "Texto colado"
        p = Path(self.target_path.get())
        if not p.exists():
            raise ValueError("Selecione um arquivo válido.")
        return extract_text(p), p.name

    def start(self):
        try:
            text, name = self.get_input()
            if len(word_tokens(text)) < 90:
                raise ValueError("Use pelo menos 90 palavras para uma análise útil.")
        except Exception as e:
            messagebox.showerror("Entrada inválida", str(e))
            return
        self.analyze_btn.configure(state="disabled")
        self.pdf_btn.configure(state="disabled")
        self.progress.start(10)
        self.status.set("Iniciando análise...")
        threading.Thread(target=self.run_analysis, args=(text,name), daemon=True).start()

    def run_analysis(self, text, name):
        try:
            authorial_text, exclusions = prepare_plagiarism_text(text)
            if len(word_tokens(authorial_text)) < 90:
                raise RuntimeError("Após excluir citações diretas devidamente referenciadas e a seção de referências, restou texto autoral insuficiente para uma análise confiável.")
            web = internet_similarity(text, self.depth.get(), self.set_status_threadsafe)
            ai = ai_analysis(authorial_text, self.set_status_threadsafe)
            self.result = {"name":name, "text":text, "authorial_text":authorial_text, "exclusions":exclusions, "web":web, "ai":ai}
            self.after(0, self.render)
        except Exception as e:
            self.after(0, lambda: self.fail(str(e)))

    def fail(self, msg):
        self.progress.stop()
        self.analyze_btn.configure(state="normal")
        self.status.set("Falha.")
        messagebox.showerror("Análise não concluída", msg)

    def render(self):
        self.progress.stop()
        self.analyze_btn.configure(state="normal")
        self.pdf_btn.configure(state="normal")
        self.status.set("Concluído.")
        r = self.result
        web = r["web"]
        ai = r["ai"]
        ai_pct = "INCONCLUSIVO" if ai.get("percentage") is None else f"{ai['percentage']:.1f}%"
        lines = [
            f"Documento: {r['name']}",
            f"Palavras totais: {len(word_tokens(r['text']))}",
            f"Palavras autorais analisadas: {len(word_tokens(r.get('authorial_text', r['text'])))}",
            "",
            f"SIMILARIDADE PROBLEMÁTICA / ANTІPLÁGIO NA WEB: {web['percentage']:.1f}%",
            web.get("status",""),
            f"Palavras desconsideradas por citação direta/referências: {(web.get('exclusions') or {}).get('excluded_words_total',0)}",
            "",
            f"TEXTO COM SINAL FORTE SUSTENTADO DE IA: {ai_pct}",
            f"Classificação: {ai.get('classification','Inconclusivo')}",
            ai.get("reason",""),
            "",
            "Principais fontes encontradas:"
        ]
        for m in web.get("matches", [])[:10]:
            lines += [f"- {m.similarity:.1f}% | {m.title}", f"  {m.url}", f"  {m.evidence}"]
        cal = ai.get("calibration") or {}
        if cal:
            fpr = cal.get("test_human_strong_fpr", cal.get("test_human_false_positive_rate"))
            det = cal.get("test_ai_strong_detection", cal.get("test_ai_detection_rate"))
            lines += ["", f"Sinal moderado (não contado no percentual principal): {ai.get('uncertain_percentage',0):.1f}%"]
            lines += [f"Sinal forte isolado (não contado sem corroboracao): {ai.get('isolated_strong_percentage',0):.1f}%"]
            if cal.get("calibration_human_n"):
                lines += [f"Base humana de calibracao: {cal.get('calibration_human_n')} textos; teste humano independente: {cal.get('test_human_n','n/d')} textos."]
            if fpr is not None:
                lines += [f"Falso positivo humano do sinal forte no teste independente: {100*fpr:.2f}% ({cal.get('test_human_n','n/d')} textos humanos)"]
            if det is not None:
                lines += [f"Detecção de IA observada no teste independente: {100*det:.2f}%"]
        self.result_text.configure(state="normal")
        self.result_text.delete("1.0","end")
        self.result_text.insert("1.0","\n".join(lines))
        self.result_text.configure(state="disabled")

    def export_pdf(self):
        if not self.result:
            return
        base = "texto_colado" if self.result["name"] == "Texto colado" else Path(self.result["name"]).stem
        p = filedialog.asksaveasfilename(defaultextension=".pdf", initialfile=base+"_relatorio.pdf", filetypes=[("PDF","*.pdf")])
        if not p:
            return
        try:
            make_report_pdf(
                Path(p), self.result["name"], self.result["web"], self.result["ai"],
                len(word_tokens(self.result.get("authorial_text", self.result["text"])))
            )
            messagebox.showinfo("Relatório gerado", f"PDF salvo em:\n{p}")
        except Exception as e:
            messagebox.showerror("Erro ao gerar PDF", str(e))

def cli_self_test():
    sample = ("A educação brasileira envolve políticas públicas, formação de professores e práticas pedagógicas. "
              "A pesquisa acadêmica deve apresentar argumentos claros, referências adequadas e metodologia coerente. " * 10)
    assert len(word_tokens(sample)) > 90
    chunks = make_search_chunks(sample, 8)
    assert chunks
    tmp = APP_DIR / "_self_test_report.pdf"
    web = {"percentage":12.5,"status":"Teste interno.","matches":[]}
    ai = {"percentage":None,"classification":"Inconclusivo","reason":"Teste interno.","blocks":[],"sampled":False,"calibration":None}
    make_report_pdf(tmp, "teste.txt", web, ai, len(word_tokens(sample)))
    assert tmp.exists() and tmp.stat().st_size > 1000
    print("SELF_TEST_OK", tmp.stat().st_size)

if __name__ == "__main__":
    if "--self-test" in sys.argv:
        cli_self_test()
    else:
        App().mainloop()
