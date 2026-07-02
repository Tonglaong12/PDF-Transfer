/* PDF Transfer Tool
   - Select (circle/drag) an area on a source PDF
   - Copy it, then place / move / resize (Shift = lock aspect ratio) it on a
     target PDF. An on-canvas raster thumbnail is used as a live preview.
   - On download, choose the export format:
       image  -> embedPng()+drawImage(): a plain Image XObject that ordinary
                 PDF editors (Foxit, Acrobat, ...) can click/move/resize/delete
                 like any picture.
       vector -> embedPage()+drawPage() with a bounding box: the real source
                 content (text stays selectable/searchable, lines stay crisp),
                 but most third-party editors treat it as one grouped object.
   - Either way, the full editable session (target PDF + every placement) is
     also embedded invisibly in the output PDF's catalog, so dragging that
     same output.pdf back in as the target here recovers everything as
     movable/deletable items. "Save Project" writes the same state to a
     standalone .json file as a lighter-weight alternative/backup.
   Runs 100% locally in the browser (pdf.js + pdf-lib loaded from ./vendor).
*/
(function () {
  "use strict";

  // Build the pdf.js worker from an inline script blob instead of pointing at
  // vendor/pdf.worker.min.js directly. When this page is opened straight from
  // disk (file:// URL) browsers give it an opaque "null" origin, and they
  // refuse to construct a Worker from a file:// script in that case. A blob:
  // URL has no such restriction, so this keeps everything working with a
  // plain double-click on index.html (no local server needed).
  (function setupWorker() {
    const el = document.getElementById("pdfWorkerSrc");
    if (el && el.textContent) {
      const blob = new Blob([el.textContent], { type: "application/javascript" });
      pdfjsLib.GlobalWorkerOptions.workerSrc = URL.createObjectURL(blob);
    } else {
      // fallback if the inline copy is missing for some reason
      pdfjsLib.GlobalWorkerOptions.workerSrc = "vendor/pdf.worker.min.js";
    }
  })();

  const DISPLAY_WIDTH = 650; // px, page rendered to roughly this width
  const CAPTURE_DPI = 200;   // resolution used when cropping the selected region
  const HANDLE_SIZE = 12;    // px, resize handle hit box
  const DELETE_SIZE = 16;    // px, delete button hit box
  const MIN_SIZE_PT = 8;     // minimum placement size in PDF points

  // ---------- state ----------
  const srcState = { pdfDoc: null, pageNum: 1, page: null, viewport: null, scale: 1 };
  const tgtState = { pdfDoc: null, pageNum: 1, page: null, viewport: null, scale: 1, originalBytes: null };

  // clipboard: { previewDataUrl, wPdf, hPdf, boundingBox:{left,bottom,right,top},
  //              sourceBytes, sourcePageIndex }
  let clipboard = null;
  // placements: { id, page, xPdf, yPdf, wPdf, hPdf, previewDataUrl, img,
  //               boundingBox, sourceBytes, sourcePageIndex }
  const placements = [];
  let selectedId = null;

  // source selection-drawing state
  let selecting = false;
  let selStart = null;
  let curRect = null;

  // target drag state
  let dragMode = null; // 'move' | 'resize' | null
  let dragInfo = null;

  // target eraser state — punches a transparent hole in the *raster* image
  // of the selected placement, for removing one unwanted line/number that got
  // swept into a rectangular selection along with the part actually wanted.
  // Only affects "image" export mode (vector export re-reads the untouched
  // source PDF content and has no concept of an erased pixel region).
  let erasing = false;
  let eraseDrawing = false;
  let eraseStart = null;
  let curEraseRect = null;
  const ERASE_COLOR_TOLERANCE = 60; // 0-255ish combined-channel tolerance for "click a line, erase just that line"

  // "erase whole line" state — single click (not a drag) on a line inside the
  // selected placement, flood-fills outward from that pixel and erases only
  // the connected stroke of similar colour, so a line that happens to touch
  // or cross a nearby letter can be removed without eating into the text.
  let erasingLine = false;

  // Undo support for the eraser tools. Every erase (rectangle or flood-fill)
  // pushes one entry recording the small "before" patch of pixels it removed
  // plus where that patch belongs, onto both a global chronological stack
  // (for Ctrl+Z, "undo whatever was erased most recently, anywhere") and the
  // owning placement's own history (for "Reverse", which restores a specific
  // patch you click on regardless of when it was erased).
  const undoStack = [];

  // "Reverse" state — single click on/near a previously-erased spot restores
  // just that patch, even if other erases happened after it.
  let reversing = false;

  // "Mask" tool — draws a solid-colour rectangle directly onto the *target*
  // PDF page itself (not tied to any placement). Used to permanently hide
  // original content that's already printed on the target PDF (e.g. a
  // template's default numbers) before pasting new content on top of it.
  // Unlike the eraser tools above, this needs no placement selected first —
  // it becomes its own placement (type: "mask") so it can still be moved,
  // resized, or deleted afterwards like anything else placed on the page.
  let masking = false;
  let maskDrawing = false;
  let maskStart = null;
  let curMaskRect = null;

  // ---------- element refs ----------
  const srcFile = document.getElementById("srcFile");
  const tgtFile = document.getElementById("tgtFile");
  const srcWrap = document.getElementById("srcWrap");
  const tgtWrap = document.getElementById("tgtWrap");
  const srcEmpty = document.getElementById("srcEmpty");
  const tgtEmpty = document.getElementById("tgtEmpty");
  const srcPrev = document.getElementById("srcPrev");
  const srcNext = document.getElementById("srcNext");
  const tgtPrev = document.getElementById("tgtPrev");
  const tgtNext = document.getElementById("tgtNext");
  const srcPageLabel = document.getElementById("srcPageLabel");
  const tgtPageLabel = document.getElementById("tgtPageLabel");
  const copyBtn = document.getElementById("copyBtn");
  const downloadBtn = document.getElementById("downloadBtn");
  const clipboardPreview = document.getElementById("clipboardPreview");
  const clipStatus = document.getElementById("clipStatus");
  const placementCount = document.getElementById("placementCount");
  const eraseBtn = document.getElementById("eraseBtn");
  const eraseLineBtn = document.getElementById("eraseLineBtn");
  const reverseBtn = document.getElementById("reverseBtn");
  const undoBtn = document.getElementById("undoBtn");
  const maskBtn = document.getElementById("maskBtn");
  const maskColorInput = document.getElementById("maskColor");

  let srcCanvas = null, srcOverlay = null;
  let tgtCanvas = null, tgtOverlay = null;

  function buildCanvasPair(wrapEl, baseId, overlayId) {
    wrapEl.innerHTML = "";
    const base = document.createElement("canvas");
    base.id = baseId;
    const overlay = document.createElement("canvas");
    overlay.id = overlayId;
    overlay.className = "overlay";
    wrapEl.appendChild(base);
    wrapEl.appendChild(overlay);
    return { base, overlay };
  }

  // ---------- helpers ----------
  function clamp(v, lo, hi) { return Math.max(lo, Math.min(hi, v)); }

  function dataUrlToUint8Array(dataUrl) {
    const base64 = dataUrl.split(",")[1];
    const binary = atob(base64);
    const bytes = new Uint8Array(binary.length);
    for (let i = 0; i < binary.length; i++) bytes[i] = binary.charCodeAt(i);
    return bytes;
  }

  // base64 <-> Uint8Array, used for saving/loading project files. Chunked to
  // avoid blowing the call stack on String.fromCharCode.apply for big PDFs.
  function uint8ToBase64(bytes) {
    let binary = "";
    const chunkSize = 0x8000;
    for (let i = 0; i < bytes.length; i += chunkSize) {
      binary += String.fromCharCode.apply(null, bytes.subarray(i, i + chunkSize));
    }
    return btoa(binary);
  }
  function base64ToUint8(b64) {
    const binary = atob(b64);
    const bytes = new Uint8Array(binary.length);
    for (let i = 0; i < binary.length; i++) bytes[i] = binary.charCodeAt(i);
    return bytes;
  }

  function pointerPos(evt, canvas) {
    const rect = canvas.getBoundingClientRect();
    return { x: evt.clientX - rect.left, y: evt.clientY - rect.top };
  }

  // ---------- PDF loading ----------
  async function loadPdfFile(file, state, isSource) {
    const bytes = new Uint8Array(await file.arrayBuffer());
    await loadPdfBytes(bytes, state, isSource);
  }

  async function loadPdfBytes(bytes, state, isSource) {
    state.originalBytes = bytes;
    state.pdfDoc = await pdfjsLib.getDocument({ data: bytes.slice() }).promise;
    state.pageNum = 1;

    if (isSource) {
      srcEmpty.remove ? null : null;
      const pair = buildCanvasPair(srcWrap, "srcCanvas", "srcOverlay");
      srcCanvas = pair.base; srcOverlay = pair.overlay;
      attachSourceEvents();
    } else {
      const pair = buildCanvasPair(tgtWrap, "tgtCanvas", "tgtOverlay");
      tgtCanvas = pair.base; tgtOverlay = pair.overlay;
      attachTargetEvents();
      if (maskBtn) maskBtn.disabled = false;
    }

    const first = await state.pdfDoc.getPage(1);
    const unscaled = first.getViewport({ scale: 1 });
    state.scale = DISPLAY_WIDTH / unscaled.width;

    if (isSource) {
      await renderSourcePage();
    } else {
      await renderTargetPage();
    }
  }

  async function renderSourcePage() {
    const page = await srcState.pdfDoc.getPage(srcState.pageNum);
    const viewport = page.getViewport({ scale: srcState.scale });
    srcCanvas.width = srcOverlay.width = Math.ceil(viewport.width);
    srcCanvas.height = srcOverlay.height = Math.ceil(viewport.height);
    await page.render({ canvasContext: srcCanvas.getContext("2d"), viewport }).promise;
    srcState.page = page;
    srcState.viewport = viewport;
    curRect = null;
    copyBtn.disabled = true;
    clearOverlay(srcOverlay);
    srcPageLabel.textContent = `หน้า ${srcState.pageNum} / ${srcState.pdfDoc.numPages}`;
    srcPrev.disabled = srcState.pageNum <= 1;
    srcNext.disabled = srcState.pageNum >= srcState.pdfDoc.numPages;
  }

  async function renderTargetPage() {
    const page = await tgtState.pdfDoc.getPage(tgtState.pageNum);
    const viewport = page.getViewport({ scale: tgtState.scale });
    tgtCanvas.width = tgtOverlay.width = Math.ceil(viewport.width);
    tgtCanvas.height = tgtOverlay.height = Math.ceil(viewport.height);
    await page.render({ canvasContext: tgtCanvas.getContext("2d"), viewport }).promise;
    tgtState.page = page;
    tgtState.viewport = viewport;
    tgtPageLabel.textContent = `หน้า ${tgtState.pageNum} / ${tgtState.pdfDoc.numPages}`;
    tgtPrev.disabled = tgtState.pageNum <= 1;
    tgtNext.disabled = tgtState.pageNum >= tgtState.pdfDoc.numPages;
    drawTargetOverlay();
    updatePlacementCount();
  }

  function clearOverlay(canvas) {
    canvas.getContext("2d").clearRect(0, 0, canvas.width, canvas.height);
  }

  // ---------- source: draw selection rectangle ----------
  function attachSourceEvents() {
    srcOverlay.onpointerdown = (e) => {
      if (!srcState.page) return;
      const p = pointerPos(e, srcOverlay);
      selecting = true;
      selStart = p;
      curRect = null;
      srcOverlay.setPointerCapture(e.pointerId);
    };
    srcOverlay.onpointermove = (e) => {
      if (!selecting) return;
      const p = pointerPos(e, srcOverlay);
      const x0 = clamp(Math.min(selStart.x, p.x), 0, srcOverlay.width);
      const y0 = clamp(Math.min(selStart.y, p.y), 0, srcOverlay.height);
      const x1 = clamp(Math.max(selStart.x, p.x), 0, srcOverlay.width);
      const y1 = clamp(Math.max(selStart.y, p.y), 0, srcOverlay.height);
      curRect = { x: x0, y: y0, w: x1 - x0, h: y1 - y0 };
      drawSourceSelection();
    };
    srcOverlay.onpointerup = () => {
      selecting = false;
      copyBtn.disabled = !curRect || curRect.w < 4 || curRect.h < 4;
    };
  }

  function drawSourceSelection() {
    clearOverlay(srcOverlay);
    if (!curRect) return;
    const ctx = srcOverlay.getContext("2d");
    ctx.save();
    ctx.fillStyle = "rgba(37,99,235,0.15)";
    ctx.fillRect(curRect.x, curRect.y, curRect.w, curRect.h);
    ctx.strokeStyle = "#2563eb";
    ctx.lineWidth = 1.5;
    ctx.setLineDash([5, 4]);
    ctx.strokeRect(curRect.x, curRect.y, curRect.w, curRect.h);
    ctx.restore();
  }

  // ---------- copy selection ----------
  // Records the *real* PDF bounding box of the selection (so export can embed
  // actual vector/text content via pdf-lib's embedPage), plus a small raster
  // snapshot used only to render a live thumbnail while the user is placing
  // and adjusting it on the target canvas.
  async function copySelection() {
    if (!curRect || curRect.w < 4 || curRect.h < 4 || !srcState.page) return;

    // -- PDF-space bounding box of the selection (this is what actually gets embedded) --
    const [x0, y0] = srcState.viewport.convertToPdfPoint(curRect.x, curRect.y);
    const [x1, y1] = srcState.viewport.convertToPdfPoint(curRect.x + curRect.w, curRect.y + curRect.h);
    const boundingBox = {
      left: Math.min(x0, x1), right: Math.max(x0, x1),
      bottom: Math.min(y0, y1), top: Math.max(y0, y1),
    };
    const wPdf = boundingBox.right - boundingBox.left;
    const hPdf = boundingBox.top - boundingBox.bottom;

    // -- raster snapshot, used for the live preview AND for "image" export mode --
    // Rendered with a transparent backdrop (background: "rgba(0,0,0,0)") instead
    // of pdf.js's default opaque white fill, so any part of the selection that
    // has no ink (e.g. the empty area around a curve line) stays see-through.
    // Without this, every placement — even a thin graph line — would carry an
    // opaque white/whatever-colour rectangle with it and blank out the target
    // page's own grid underneath wherever it's dropped or dragged.
    const captureScale = CAPTURE_DPI / 72;
    const viewportHi = srcState.page.getViewport({ scale: captureScale });
    const hiCanvas = document.createElement("canvas");
    hiCanvas.width = Math.ceil(viewportHi.width);
    hiCanvas.height = Math.ceil(viewportHi.height);
    await srcState.page.render({
      canvasContext: hiCanvas.getContext("2d"),
      viewport: viewportHi,
      background: "rgba(0,0,0,0)",
    }).promise;

    const ratio = captureScale / srcState.scale;
    const sx = curRect.x * ratio, sy = curRect.y * ratio;
    const sw = curRect.w * ratio, sh = curRect.h * ratio;
    const off = document.createElement("canvas");
    off.width = Math.max(1, Math.round(sw));
    off.height = Math.max(1, Math.round(sh));
    off.getContext("2d").drawImage(hiCanvas, sx, sy, sw, sh, 0, 0, off.width, off.height);
    const previewDataUrl = off.toDataURL("image/png");

    clipboard = {
      previewDataUrl, wPdf, hPdf, boundingBox,
      sourceBytes: srcState.originalBytes,
      sourcePageIndex: srcState.pageNum - 1,
    };
    renderClipboardPreview();
  }

  function renderClipboardPreview() {
    clipboardPreview.innerHTML = "";
    if (!clipboard) {
      clipStatus.textContent = "ยังไม่ได้คัดลอกส่วนใด";
      return;
    }
    const img = document.createElement("img");
    img.src = clipboard.previewDataUrl;
    clipboardPreview.appendChild(img);
    clipStatus.textContent = `พร้อมวาง (ขนาดประมาณ ${clipboard.wPdf.toFixed(0)}×${clipboard.hPdf.toFixed(0)} pt) — คลิกตำแหน่งบน PDF ปลายทาง`;
  }

  // ---------- target: place / move / resize / delete ----------
  function attachTargetEvents() {
    tgtOverlay.onpointerdown = (e) => {
      if (!tgtState.page) return;
      const p = pointerPos(e, tgtOverlay);

      // -3) "mask" tool active: drag a rectangle directly onto the target
      // page to create a solid-colour cover placement. No placement needs
      // to be selected first — this acts on the target page itself.
      if (masking) {
        maskDrawing = true;
        maskStart = p;
        curMaskRect = null;
        tgtOverlay.setPointerCapture(e.pointerId);
        return;
      }

      // -2) "reverse" tool active: a single click restores whichever erased
      // patch on the selected placement is nearest to the click.
      if (reversing) {
        const pl = placements.find((x) => x.id === selectedId && x.page === tgtState.pageNum);
        if (pl) reverseNearClick(pl, p);
        return;
      }

      // -1) "erase whole line" tool active: a single click flood-fills and
      // erases just the connected line/stroke under the cursor.
      if (erasingLine) {
        const pl = placements.find((x) => x.id === selectedId && x.page === tgtState.pageNum);
        if (pl) floodFillErase(pl, p);
        return;
      }

      // 0) eraser tool active: draw an erase rectangle instead of the normal
      // select/move/resize/place interactions below.
      if (erasing) {
        eraseDrawing = true;
        eraseStart = p;
        curEraseRect = null;
        tgtOverlay.setPointerCapture(e.pointerId);
        return;
      }

      // 1) hit-test delete button of the selected placement
      const sel = placements.find((pl) => pl.id === selectedId && pl.page === tgtState.pageNum);
      if (sel) {
        const r = canvasRectFor(sel);
        if (Math.abs(p.x - (r.left + r.width)) <= DELETE_SIZE / 2 + 4 &&
            Math.abs(p.y - r.top) <= DELETE_SIZE / 2 + 4) {
          placements.splice(placements.indexOf(sel), 1);
          selectedId = null;
          drawTargetOverlay();
          updatePlacementCount();
          return;
        }
        // 2) hit-test resize handle
        if (Math.abs(p.x - (r.left + r.width)) <= HANDLE_SIZE / 2 + 4 &&
            Math.abs(p.y - (r.top + r.height)) <= HANDLE_SIZE / 2 + 4) {
          dragMode = "resize";
          dragInfo = {
            id: sel.id,
            startX: p.x, startY: p.y,
            leftPdf0: sel.xPdf,
            topPdf0: sel.yPdf + sel.hPdf,
            wPdf0: sel.wPdf, hPdf0: sel.hPdf,
          };
          tgtOverlay.setPointerCapture(e.pointerId);
          return;
        }
      }

      // 3) hit-test any placement box on this page (topmost last)
      const onPage = placements.filter((pl) => pl.page === tgtState.pageNum);
      for (let i = onPage.length - 1; i >= 0; i--) {
        const pl = onPage[i];
        const r = canvasRectFor(pl);
        if (p.x >= r.left && p.x <= r.left + r.width && p.y >= r.top && p.y <= r.top + r.height) {
          selectedId = pl.id;
          dragMode = "move";
          dragInfo = { id: pl.id, startX: p.x, startY: p.y, xPdf0: pl.xPdf, yPdf0: pl.yPdf };
          tgtOverlay.setPointerCapture(e.pointerId);
          drawTargetOverlay();
          return;
        }
      }

      // 4) empty area: place new item from clipboard
      if (clipboard) {
        const [pdfX, pdfY] = tgtState.viewport.convertToPdfPoint(p.x, p.y);
        const w = clipboard.wPdf, h = clipboard.hPdf;
        const item = {
          id: "p" + Date.now() + Math.random().toString(36).slice(2, 7),
          page: tgtState.pageNum,
          xPdf: pdfX - w / 2,
          yPdf: pdfY - h / 2,
          wPdf: w, hPdf: h,
          previewDataUrl: clipboard.previewDataUrl,
          img: null,
          boundingBox: clipboard.boundingBox,
          sourceBytes: clipboard.sourceBytes,
          sourcePageIndex: clipboard.sourcePageIndex,
          eraseHistory: [],
        };
        item.img = preloadImage(item.previewDataUrl, item);
        placements.push(item);
        selectedId = item.id;
        drawTargetOverlay();
        updatePlacementCount();
      } else {
        selectedId = null;
        drawTargetOverlay();
      }
    };

    tgtOverlay.onpointermove = (e) => {
      if (maskDrawing) {
        const p = pointerPos(e, tgtOverlay);
        const x0 = clamp(Math.min(maskStart.x, p.x), 0, tgtOverlay.width);
        const y0 = clamp(Math.min(maskStart.y, p.y), 0, tgtOverlay.height);
        const x1 = clamp(Math.max(maskStart.x, p.x), 0, tgtOverlay.width);
        const y1 = clamp(Math.max(maskStart.y, p.y), 0, tgtOverlay.height);
        curMaskRect = { x: x0, y: y0, w: x1 - x0, h: y1 - y0 };
        drawTargetOverlay();
        return;
      }
      if (eraseDrawing) {
        const p = pointerPos(e, tgtOverlay);
        const x0 = clamp(Math.min(eraseStart.x, p.x), 0, tgtOverlay.width);
        const y0 = clamp(Math.min(eraseStart.y, p.y), 0, tgtOverlay.height);
        const x1 = clamp(Math.max(eraseStart.x, p.x), 0, tgtOverlay.width);
        const y1 = clamp(Math.max(eraseStart.y, p.y), 0, tgtOverlay.height);
        curEraseRect = { x: x0, y: y0, w: x1 - x0, h: y1 - y0 };
        drawTargetOverlay();
        return;
      }
      if (!dragMode) return;
      const p = pointerPos(e, tgtOverlay);
      const pl = placements.find((x) => x.id === dragInfo.id);
      if (!pl) return;
      const dx = p.x - dragInfo.startX;
      const dy = p.y - dragInfo.startY;
      if (dragMode === "move") {
        pl.xPdf = dragInfo.xPdf0 + dx / tgtState.scale;
        pl.yPdf = dragInfo.yPdf0 - dy / tgtState.scale;
      } else if (dragMode === "resize") {
        let newW = dragInfo.wPdf0 + dx / tgtState.scale;
        let newH = dragInfo.hPdf0 + dy / tgtState.scale;
        if (e.shiftKey) {
          // Hold Shift to keep the original aspect ratio: drive the resize
          // from whichever axis the user is dragging further along.
          const aspect = dragInfo.wPdf0 / dragInfo.hPdf0;
          const wDelta = Math.abs(newW - dragInfo.wPdf0);
          const hDelta = Math.abs(newH - dragInfo.hPdf0);
          if (wDelta >= hDelta * aspect) {
            newH = newW / aspect;
          } else {
            newW = newH * aspect;
          }
        }
        newW = Math.max(MIN_SIZE_PT, newW);
        newH = Math.max(MIN_SIZE_PT, newH);
        pl.wPdf = newW;
        pl.hPdf = newH;
        pl.xPdf = dragInfo.leftPdf0;
        pl.yPdf = dragInfo.topPdf0 - newH;
      }
      drawTargetOverlay();
    };

    tgtOverlay.onpointerup = () => {
      if (maskDrawing) {
        maskDrawing = false;
        const rect = curMaskRect;
        curMaskRect = null;
        if (rect && rect.w > 2 && rect.h > 2) {
          createMaskPlacement(rect);
        } else {
          drawTargetOverlay();
        }
        return;
      }
      if (eraseDrawing) {
        eraseDrawing = false;
        const rect = curEraseRect;
        curEraseRect = null;
        const pl = placements.find((x) => x.id === selectedId && x.page === tgtState.pageNum);
        if (pl && rect && rect.w > 2 && rect.h > 2) {
          applyEraseToPlacement(pl, rect);
        } else {
          drawTargetOverlay();
        }
        return;
      }
      dragMode = null;
      dragInfo = null;
    };
  }

  // Builds a new solid-colour "mask" placement from a rectangle drawn in
  // target-canvas pixel space. This covers whatever original PDF content is
  // underneath permanently in the exported file — unlike the eraser tools,
  // it has no source image of its own, it's just a filled rectangle. Gets
  // selected immediately afterwards so it can be nudged/resized right away,
  // and normal copied content can then be pasted on top of it as usual.
  function createMaskPlacement(canvasRect) {
    const [x0, y0] = tgtState.viewport.convertToPdfPoint(canvasRect.x, canvasRect.y);
    const [x1, y1] = tgtState.viewport.convertToPdfPoint(canvasRect.x + canvasRect.w, canvasRect.y + canvasRect.h);
    const xPdf = Math.min(x0, x1), yPdf = Math.min(y0, y1);
    const wPdf = Math.max(MIN_SIZE_PT, Math.abs(x1 - x0));
    const hPdf = Math.max(MIN_SIZE_PT, Math.abs(y1 - y0));
    const color = (maskColorInput && maskColorInput.value) || "#ffffff";
    const item = {
      id: "m" + Date.now() + Math.random().toString(36).slice(2, 7),
      type: "mask",
      page: tgtState.pageNum,
      xPdf, yPdf, wPdf, hPdf,
      color,
      img: null,
      eraseHistory: [],
    };
    placements.push(item);
    selectedId = item.id;
    drawTargetOverlay();
    updatePlacementCount();
  }

  // Punches a transparent hole into the selected placement's own raster image
  // wherever the erase rectangle (in target-canvas pixel space) overlaps it.
  // Works entirely in the placement's local pixel space so it stays correct
  // regardless of how the placement has been moved/resized on the target page.
  function applyEraseToPlacement(pl, canvasRect) {
    const [ex0, ey0] = tgtState.viewport.convertToPdfPoint(canvasRect.x, canvasRect.y);
    const [ex1, ey1] = tgtState.viewport.convertToPdfPoint(canvasRect.x + canvasRect.w, canvasRect.y + canvasRect.h);
    const eLeft = Math.min(ex0, ex1), eRight = Math.max(ex0, ex1);
    const eBottom = Math.min(ey0, ey1), eTop = Math.max(ey0, ey1);

    // Clip the erase rectangle to the placement's own PDF-space box.
    const pLeft = pl.xPdf, pRight = pl.xPdf + pl.wPdf;
    const pBottom = pl.yPdf, pTop = pl.yPdf + pl.hPdf;
    const cLeft = Math.max(eLeft, pLeft), cRight = Math.min(eRight, pRight);
    const cBottom = Math.max(eBottom, pBottom), cTop = Math.min(eTop, pTop);
    if (cRight <= cLeft || cTop <= cBottom) {
      drawTargetOverlay();
      return; // erase rectangle didn't actually overlap this placement
    }

    // Fractional position within the placement (0..1, origin at its bottom-left).
    const fx0 = (cLeft - pLeft) / pl.wPdf, fx1 = (cRight - pLeft) / pl.wPdf;
    const fy0 = (cBottom - pBottom) / pl.hPdf, fy1 = (cTop - pBottom) / pl.hPdf;

    const img = new Image();
    img.onload = () => {
      const w = img.naturalWidth, h = img.naturalHeight;
      const canvas = document.createElement("canvas");
      canvas.width = w;
      canvas.height = h;
      const ctx = canvas.getContext("2d");
      ctx.drawImage(img, 0, 0, w, h);
      // Raster pixel space has y=0 at the top, so flip the fractional y range.
      const px0 = Math.round(fx0 * w), px1 = Math.round(fx1 * w);
      const py0 = Math.round((1 - fy1) * h), py1 = Math.round((1 - fy0) * h);
      const ew = Math.max(1, px1 - px0), eh = Math.max(1, py1 - py0);

      // Save the "before" pixels so this specific erase can be reversed later.
      const patchCanvas = document.createElement("canvas");
      patchCanvas.width = ew;
      patchCanvas.height = eh;
      patchCanvas.getContext("2d").drawImage(canvas, px0, py0, ew, eh, 0, 0, ew, eh);
      const beforeDataUrl = patchCanvas.toDataURL("image/png");

      ctx.clearRect(px0, py0, ew, eh);
      pl.previewDataUrl = canvas.toDataURL("image/png");
      pl.img = preloadImage(pl.previewDataUrl, pl);
      pl.erased = true; // see exportPdf(): once a placement has been edited by an
                         // eraser tool, it's embedded as an image even in "vector"
                         // export mode, since the erased pixels only exist in this
                         // raster snapshot — the real vector source PDF has no idea
                         // anything was erased and would just draw the original back.
      pushEraseHistory(pl, { x: px0, y: py0, w: ew, h: eh, beforeDataUrl });
      drawTargetOverlay();
    };
    img.src = pl.previewDataUrl;
  }

  // Searches outward in expanding rings from (cx,cy) for the nearest pixel
  // that isn't fully transparent. The raster crop is usually captured at a
  // much higher resolution than it's displayed on screen (CAPTURE_DPI vs. the
  // on-screen scale), so a thin line can occupy under a screen-pixel's worth
  // of width — an exact-pixel click would almost always miss it. This makes
  // clicking "near" a line count as clicking "on" it.
  function findNearestInkPixel(data, w, h, cx, cy, maxRadius) {
    const a = (x, y) => data[(y * w + x) * 4 + 3];
    if (cx >= 0 && cx < w && cy >= 0 && cy < h && a(cx, cy) !== 0) return [cx, cy];
    for (let r = 1; r <= maxRadius; r++) {
      for (let dx = -r; dx <= r; dx++) {
        for (let dy = -r; dy <= r; dy++) {
          if (Math.max(Math.abs(dx), Math.abs(dy)) !== r) continue; // only the ring at this radius
          const x = cx + dx, y = cy + dy;
          if (x < 0 || x >= w || y < 0 || y >= h) continue;
          if (a(x, y) !== 0) return [x, y];
        }
      }
    }
    return null;
  }

  // Erases just the connected stroke of similar colour under a single click,
  // via flood fill — so a line that touches or crosses nearby text can be
  // removed without eating into the letters next to it (as long as there's
  // at least a hairline visual gap between the line and the text pixels).
  function floodFillErase(pl, canvasPoint) {
    const [pdfX, pdfY] = tgtState.viewport.convertToPdfPoint(canvasPoint.x, canvasPoint.y);
    const fx = (pdfX - pl.xPdf) / pl.wPdf;
    const fy = (pdfY - pl.yPdf) / pl.hPdf;
    if (fx < 0 || fx > 1 || fy < 0 || fy > 1) return; // click missed this placement

    const img = new Image();
    img.onload = () => {
      const w = img.naturalWidth, h = img.naturalHeight;
      const canvas = document.createElement("canvas");
      canvas.width = w;
      canvas.height = h;
      const ctx = canvas.getContext("2d");
      ctx.drawImage(img, 0, 0, w, h);
      const imageData = ctx.getImageData(0, 0, w, h);
      const data = imageData.data;

      const clickX = clamp(Math.round(fx * w), 0, w - 1);
      const clickY = clamp(Math.round((1 - fy) * h), 0, h - 1); // pixel space is top-down
      const seed = findNearestInkPixel(data, w, h, clickX, clickY, 24);
      if (!seed) {
        showTempStatus("ไม่พบเส้น/จุดสีใกล้ตำแหน่งที่คลิก ลองคลิกให้ตรงเส้นมากขึ้น");
        return;
      }
      const [startX, startY] = seed;
      const idx = (x, y) => (y * w + x) * 4;
      const s = idx(startX, startY);
      const startA = data[s + 3];
      const startR = data[s], startG = data[s + 1], startB = data[s + 2];
      const tol2 = ERASE_COLOR_TOLERANCE * ERASE_COLOR_TOLERANCE;

      // Keep an untouched copy of the original pixels so the erased region's
      // "before" patch can be saved for undo, once we know its bounding box.
      const originalData = new Uint8ClampedArray(data);

      const visited = new Uint8Array(w * h);
      const stack = [[startX, startY]];
      let minX = startX, maxX = startX, minY = startY, maxY = startY;
      let erasedAny = false;
      while (stack.length) {
        const [x, y] = stack.pop();
        if (x < 0 || x >= w || y < 0 || y >= h) continue;
        const vi = y * w + x;
        if (visited[vi]) continue;
        const i = idx(x, y);
        const a = data[i + 3];
        if (a === 0) continue; // transparent pixels act as the boundary
        const dr = data[i] - startR, dg = data[i + 1] - startG, db = data[i + 2] - startB, da = a - startA;
        if (dr * dr + dg * dg + db * db + da * da > tol2 * 4) continue;
        visited[vi] = 1;
        data[i + 3] = 0; // make transparent
        erasedAny = true;
        if (x < minX) minX = x;
        if (x > maxX) maxX = x;
        if (y < minY) minY = y;
        if (y > maxY) maxY = y;
        stack.push([x + 1, y], [x - 1, y], [x, y + 1], [x, y - 1]);
      }
      if (!erasedAny) return;

      const patchW = maxX - minX + 1, patchH = maxY - minY + 1;
      const origCanvas = document.createElement("canvas");
      origCanvas.width = w;
      origCanvas.height = h;
      origCanvas.getContext("2d").putImageData(new ImageData(originalData, w, h), 0, 0);
      const patchCanvas = document.createElement("canvas");
      patchCanvas.width = patchW;
      patchCanvas.height = patchH;
      patchCanvas.getContext("2d").drawImage(origCanvas, minX, minY, patchW, patchH, 0, 0, patchW, patchH);
      const beforeDataUrl = patchCanvas.toDataURL("image/png");

      ctx.putImageData(imageData, 0, 0);
      pl.previewDataUrl = canvas.toDataURL("image/png");
      pl.img = preloadImage(pl.previewDataUrl, pl);
      pl.erased = true; // see exportPdf(): forces this placement to embed as an
                         // image even in "vector" export mode, so the erased line
                         // actually stays erased instead of the real vector source
                         // content getting redrawn whole again.
      pushEraseHistory(pl, { x: minX, y: minY, w: patchW, h: patchH, beforeDataUrl });
      drawTargetOverlay();
    };
    img.src = pl.previewDataUrl;
  }

  // ---------- undo / reverse for the eraser tools ----------
  function pushEraseHistory(pl, entry) {
    entry.placementId = pl.id;
    (pl.eraseHistory || (pl.eraseHistory = [])).push(entry);
    undoStack.push(entry);
  }

  function removeEraseEntry(pl, entry) {
    if (pl && pl.eraseHistory) {
      const i = pl.eraseHistory.indexOf(entry);
      if (i !== -1) pl.eraseHistory.splice(i, 1);
    }
    const j = undoStack.indexOf(entry);
    if (j !== -1) undoStack.splice(j, 1);
  }

  // Pastes one saved "before" patch back onto its placement's current raster,
  // undoing exactly that one erase (rectangle or flood-fill) regardless of
  // whether other erases happened afterwards.
  function restoreErasePatch(entry) {
    const pl = placements.find((x) => x.id === entry.placementId);
    removeEraseEntry(pl, entry);
    if (!pl) return; // placement itself was deleted since this entry was recorded
    const baseImg = new Image();
    baseImg.onerror = () => {
      console.error("undo failed: could not reload placement image for", pl.id);
      showTempStatus("ย้อนกลับไม่สำเร็จ (โหลดภาพเดิมไม่ได้)");
    };
    baseImg.onload = () => {
      const w = baseImg.naturalWidth, h = baseImg.naturalHeight;
      const canvas = document.createElement("canvas");
      canvas.width = w;
      canvas.height = h;
      const ctx = canvas.getContext("2d");
      ctx.drawImage(baseImg, 0, 0, w, h);
      const patchImg = new Image();
      patchImg.onerror = () => {
        console.error("undo failed: could not reload saved patch for", pl.id, entry);
        showTempStatus("ย้อนกลับไม่สำเร็จ (โหลดส่วนที่บันทึกไว้ไม่ได้)");
      };
      patchImg.onload = () => {
        // clear first: the saved patch may itself contain transparent pixels
        // (e.g. it was already partly erased before), so draw, don't blend.
        ctx.clearRect(entry.x, entry.y, entry.w, entry.h);
        ctx.drawImage(patchImg, entry.x, entry.y, entry.w, entry.h);
        pl.previewDataUrl = canvas.toDataURL("image/png");
        pl.img = preloadImage(pl.previewDataUrl, pl);
        drawTargetOverlay();
      };
      patchImg.src = entry.beforeDataUrl;
    };
    baseImg.src = pl.previewDataUrl;
  }

  // Ctrl+Z: always undoes whatever erase happened most recently, on any placement.
  function undoLastErase() {
    if (!undoStack.length) {
      showTempStatus("ไม่มีการลบให้ย้อนกลับ");
      return;
    }
    restoreErasePatch(undoStack[undoStack.length - 1]);
    if (undoBtn) undoBtn.disabled = !undoStack.length;
  }

  // "Reverse" tool: click near a specific previously-erased spot on the
  // *selected* placement to bring back just the connected bit of ink under
  // the cursor — not the whole rectangle/line that erase removed. Works like
  // flood fill run "backwards": it floods through the saved *before* patch
  // (which still has real colour/alpha data) starting at the click, restores
  // only that connected chunk onto the live image, and consumes just those
  // pixels from the saved patch so the rest stays available for later clicks.
  function reverseNearClick(pl, canvasPoint) {
    const history = pl.eraseHistory;
    if (!history || !history.length) {
      showTempStatus("รายการนี้ยังไม่มีส่วนที่ถูกลบให้ย้อนกลับ");
      return;
    }
    const [pdfX, pdfY] = tgtState.viewport.convertToPdfPoint(canvasPoint.x, canvasPoint.y);
    const fx = (pdfX - pl.xPdf) / pl.wPdf;
    const fy = (pdfY - pl.yPdf) / pl.hPdf;
    if (fx < 0 || fx > 1 || fy < 0 || fy > 1 || !pl.rasterW || !pl.rasterH) return;
    const w = pl.rasterW, h = pl.rasterH;
    const clickX = clamp(Math.round(fx * w), 0, w - 1);
    const clickY = clamp(Math.round((1 - fy) * h), 0, h - 1);

    const PAD = 24; // forgiving hit-test margin, same idea as findNearestInkPixel
    const candidates = [];
    for (let i = history.length - 1; i >= 0; i--) {
      const e = history[i];
      if (clickX >= e.x - PAD && clickX <= e.x + e.w + PAD &&
          clickY >= e.y - PAD && clickY <= e.y + e.h + PAD) {
        candidates.push(e);
      }
    }
    if (!candidates.length) {
      showTempStatus("ไม่พบส่วนที่เคยลบใกล้ตำแหน่งที่คลิก");
      return;
    }
    tryReverseCandidate(pl, candidates, 0, clickX, clickY);
  }

  // Tries candidate erase-history entries (most recent first) until one
  // actually has ink near the click point, since several past erases might
  // have overlapping/nearby bounding boxes.
  function tryReverseCandidate(pl, candidates, i, clickX, clickY) {
    if (i >= candidates.length) {
      showTempStatus("ไม่พบส่วนที่เคยลบใกล้ตำแหน่งที่คลิก");
      return;
    }
    const entry = candidates[i];
    const patchImg = new Image();
    patchImg.onload = () => {
      const pw = patchImg.naturalWidth, ph = patchImg.naturalHeight;
      const patchCanvas = document.createElement("canvas");
      patchCanvas.width = pw;
      patchCanvas.height = ph;
      const pctx = patchCanvas.getContext("2d");
      pctx.drawImage(patchImg, 0, 0);
      const patchImageData = pctx.getImageData(0, 0, pw, ph);
      const pdata = patchImageData.data;

      const localX = clamp(clickX - entry.x, 0, pw - 1);
      const localY = clamp(clickY - entry.y, 0, ph - 1);
      const seed = findNearestInkPixel(pdata, pw, ph, localX, localY, 24);
      if (!seed) {
        tryReverseCandidate(pl, candidates, i + 1, clickX, clickY);
        return;
      }

      // Flood fill within the saved patch to find just the connected chunk to restore.
      const [sx, sy] = seed;
      const pidx = (x, y) => (y * pw + x) * 4;
      const s = pidx(sx, sy);
      const startR = pdata[s], startG = pdata[s + 1], startB = pdata[s + 2], startA = pdata[s + 3];
      const tol2 = ERASE_COLOR_TOLERANCE * ERASE_COLOR_TOLERANCE;
      const visited = new Uint8Array(pw * ph);
      const stack = [[sx, sy]];
      const restoredPixels = [];
      while (stack.length) {
        const [x, y] = stack.pop();
        if (x < 0 || x >= pw || y < 0 || y >= ph) continue;
        const vi = y * pw + x;
        if (visited[vi]) continue;
        const pi = pidx(x, y);
        const a = pdata[pi + 3];
        if (a === 0) continue;
        const dr = pdata[pi] - startR, dg = pdata[pi + 1] - startG, db = pdata[pi + 2] - startB, da = a - startA;
        if (dr * dr + dg * dg + db * db + da * da > tol2 * 4) continue;
        visited[vi] = 1;
        restoredPixels.push(x, y);
        stack.push([x + 1, y], [x - 1, y], [x, y + 1], [x, y - 1]);
      }
      if (!restoredPixels.length) {
        tryReverseCandidate(pl, candidates, i + 1, clickX, clickY);
        return;
      }

      const liveImg = new Image();
      liveImg.onload = () => {
        const w = liveImg.naturalWidth, h = liveImg.naturalHeight;
        const liveCanvas = document.createElement("canvas");
        liveCanvas.width = w;
        liveCanvas.height = h;
        const lctx = liveCanvas.getContext("2d");
        lctx.drawImage(liveImg, 0, 0, w, h);
        const liveImageData = lctx.getImageData(0, 0, w, h);
        const ldata = liveImageData.data;
        const lidx = (x, y) => (y * w + x) * 4;

        for (let k = 0; k < restoredPixels.length; k += 2) {
          const px = restoredPixels[k], py = restoredPixels[k + 1];
          const gx = px + entry.x, gy = py + entry.y;
          if (gx < 0 || gx >= w || gy < 0 || gy >= h) continue;
          const li = lidx(gx, gy);
          const pi = pidx(px, py);
          ldata[li] = pdata[pi]; ldata[li + 1] = pdata[pi + 1]; ldata[li + 2] = pdata[pi + 2]; ldata[li + 3] = pdata[pi + 3];
          pdata[pi + 3] = 0; // consume this pixel from the saved patch
        }
        lctx.putImageData(liveImageData, 0, 0);
        pl.previewDataUrl = liveCanvas.toDataURL("image/png");
        pl.img = preloadImage(pl.previewDataUrl, pl);

        // Keep or drop this history entry depending on whether any ink is left in it.
        let anyLeft = false;
        for (let k = 3; k < pdata.length; k += 4) { if (pdata[k] !== 0) { anyLeft = true; break; } }
        if (anyLeft) {
          pctx.putImageData(patchImageData, 0, 0);
          entry.beforeDataUrl = patchCanvas.toDataURL("image/png");
        } else {
          removeEraseEntry(pl, entry);
        }
        drawTargetOverlay();
      };
      liveImg.src = pl.previewDataUrl;
    };
    patchImg.src = entry.beforeDataUrl;
  }

  function showTempStatus(msg) {
    const prevText = placementCount.textContent;
    placementCount.textContent = msg;
    setTimeout(() => { placementCount.textContent = prevText; }, 2500);
  }

  function preloadImage(dataUrl, pl) {
    const img = new Image();
    img.onload = () => {
      if (pl) { pl.rasterW = img.naturalWidth; pl.rasterH = img.naturalHeight; }
      drawTargetOverlay();
    };
    img.src = dataUrl;
    return img;
  }

  function canvasRectFor(pl) {
    const [cx0, cy0] = tgtState.viewport.convertToViewportPoint(pl.xPdf, pl.yPdf);
    const [cx1, cy1] = tgtState.viewport.convertToViewportPoint(pl.xPdf + pl.wPdf, pl.yPdf + pl.hPdf);
    const left = Math.min(cx0, cx1), top = Math.min(cy0, cy1);
    return { left, top, width: Math.abs(cx1 - cx0), height: Math.abs(cy1 - cy0) };
  }

  function drawTargetOverlay() {
    if (!tgtOverlay) return;
    clearOverlay(tgtOverlay);
    const ctx = tgtOverlay.getContext("2d");
    const onPage = placements.filter((pl) => pl.page === tgtState.pageNum);
    for (const pl of onPage) {
      const r = canvasRectFor(pl);
      if (pl.type === "mask") {
        ctx.save();
        ctx.fillStyle = pl.color || "#ffffff";
        ctx.fillRect(r.left, r.top, r.width, r.height);
        ctx.restore();
      } else if (pl.img && pl.img.complete && pl.img.naturalWidth) {
        ctx.drawImage(pl.img, r.left, r.top, r.width, r.height);
      }
      const isSel = pl.id === selectedId;
      ctx.save();
      ctx.strokeStyle = isSel ? "#2563eb" : (pl.type === "mask" ? "rgba(5,150,105,0.55)" : "rgba(37,99,235,0.55)");
      ctx.lineWidth = isSel ? 2 : 1;
      ctx.setLineDash(isSel ? [] : [4, 3]);
      ctx.strokeRect(r.left, r.top, r.width, r.height);
      ctx.restore();

      // Hide the resize/delete handles while an eraser/mask tool is active
      // so they don't get in the way.
      if (isSel && !erasing && !erasingLine && !reversing && !masking) {
        // resize handle
        ctx.save();
        ctx.fillStyle = "#2563eb";
        ctx.beginPath();
        ctx.arc(r.left + r.width, r.top + r.height, HANDLE_SIZE / 2, 0, Math.PI * 2);
        ctx.fill();
        ctx.restore();

        // delete button
        ctx.save();
        ctx.fillStyle = "#dc2626";
        ctx.beginPath();
        ctx.arc(r.left + r.width, r.top, DELETE_SIZE / 2, 0, Math.PI * 2);
        ctx.fill();
        ctx.fillStyle = "#fff";
        ctx.font = "11px sans-serif";
        ctx.textAlign = "center";
        ctx.textBaseline = "middle";
        ctx.fillText("×", r.left + r.width, r.top + 1);
        ctx.restore();
      }
    }

    if (erasing && curEraseRect) {
      ctx.save();
      ctx.fillStyle = "rgba(220,38,38,0.25)";
      ctx.fillRect(curEraseRect.x, curEraseRect.y, curEraseRect.w, curEraseRect.h);
      ctx.strokeStyle = "#dc2626";
      ctx.lineWidth = 1.5;
      ctx.setLineDash([5, 4]);
      ctx.strokeRect(curEraseRect.x, curEraseRect.y, curEraseRect.w, curEraseRect.h);
      ctx.restore();
    }

    if (masking && curMaskRect) {
      ctx.save();
      ctx.globalAlpha = 0.7;
      ctx.fillStyle = (maskColorInput && maskColorInput.value) || "#ffffff";
      ctx.fillRect(curMaskRect.x, curMaskRect.y, curMaskRect.w, curMaskRect.h);
      ctx.globalAlpha = 1;
      ctx.strokeStyle = "#059669";
      ctx.lineWidth = 1.5;
      ctx.setLineDash([5, 4]);
      ctx.strokeRect(curMaskRect.x, curMaskRect.y, curMaskRect.w, curMaskRect.h);
      ctx.restore();
    }

    updateEraseBtnState();
  }

  function updateEraseBtnState() {
    // Mask placements have no raster image of their own, so the eraser
    // tools (which operate on a placement's pixel data) don't apply to them
    // — only real copied/pasted content is "erasable" this way.
    const sel = placements.find((pl) => pl.id === selectedId);
    const hasErasableSelection = !!sel && sel.type !== "mask";
    if (eraseBtn) {
      eraseBtn.disabled = !hasErasableSelection;
      if (!hasErasableSelection && erasing) {
        erasing = false;
        eraseBtn.classList.remove("active");
      }
    }
    if (eraseLineBtn) {
      eraseLineBtn.disabled = !hasErasableSelection;
      if (!hasErasableSelection && erasingLine) {
        erasingLine = false;
        eraseLineBtn.classList.remove("active");
      }
    }
    if (reverseBtn) {
      reverseBtn.disabled = !hasErasableSelection;
      if (!hasErasableSelection && reversing) {
        reversing = false;
        reverseBtn.classList.remove("active");
      }
    }
    if (undoBtn) {
      undoBtn.disabled = !undoStack.length;
    }
    if (tgtOverlay) {
      tgtOverlay.style.cursor = erasing || erasingLine || reversing || masking ? "crosshair" : "default";
    }
  }

  function updatePlacementCount() {
    const total = placements.length;
    const onPage = placements.filter((pl) => pl.page === tgtState.pageNum).length;
    placementCount.textContent = total
      ? `วางแล้วทั้งหมด ${total} รายการ (หน้านี้ ${onPage} รายการ)`
      : "ยังไม่มีรายการที่วาง";
  }

  // ---------- shared project-state helpers ----------
  const PROJECT_TYPE = "pdf-transfer-tool-project";
  const PROJECT_CATALOG_KEY = "PdfTransferToolProject";

  // Serializes the current editable session (the pristine target PDF, every
  // source PDF a placement was copied from, and all placements) into one
  // plain object. Used both by "Save Project" (written to a .json file) and
  // by the PDF export step (embedded invisibly inside output.pdf itself).
  function buildProjectObject() {
    const sourceIndexByBytes = new Map();
    const sources = [];
    function getSourceIndex(bytes) {
      if (!sourceIndexByBytes.has(bytes)) {
        sourceIndexByBytes.set(bytes, sources.length);
        sources.push(uint8ToBase64(bytes));
      }
      return sourceIndexByBytes.get(bytes);
    }
    return {
      type: PROJECT_TYPE,
      version: 1,
      target: { bytesBase64: uint8ToBase64(tgtState.originalBytes) },
      sources,
      placements: placements.map((pl) => ({
        type: pl.type || "content",
        page: pl.page,
        xPdf: pl.xPdf, yPdf: pl.yPdf, wPdf: pl.wPdf, hPdf: pl.hPdf,
        boundingBox: pl.boundingBox,
        sourcePageIndex: pl.sourcePageIndex,
        // "mask" placements are a plain filled rectangle with no source PDF
        // content behind them, so skip the source-bytes bookkeeping for those.
        sourceIndex: pl.type === "mask" ? undefined : getSourceIndex(pl.sourceBytes),
        previewDataUrl: pl.previewDataUrl,
        color: pl.color,
        // Cheap pre-check so exportPdf() can skip the (async, per-entry)
        // clip-hole rebuilding for placements nothing ever touched.
        erased: !!pl.erased,
        // The actual erase record: each entry's "before" patch is what lets
        // vector export rebuild the exact currently-erased hole shape (see
        // computeClipHolesForPlacement), and lets "Reverse" keep working on
        // old erases too. Unlike the undo stack (Ctrl+Z, intentionally reset
        // below — see restoreProject), this is worth carrying across a
        // reload so both of those keep working on a re-opened project.
        eraseHistory: (pl.eraseHistory || []).map((e) => ({ x: e.x, y: e.y, w: e.w, h: e.h, beforeDataUrl: e.beforeDataUrl })),
      })),
    };
  }

  // Rebuilds tgtState + placements from a project object, however it was
  // obtained (a .json project file, or one recovered from inside a PDF).
  async function restoreProject(project) {
    const sourceBytesArr = (project.sources || []).map((b64) => base64ToUint8(b64));
    const targetBytes = base64ToUint8(project.target.bytesBase64);

    await loadPdfBytes(targetBytes, tgtState, false);

    placements.length = 0;
    // The global Ctrl+Z stack only ever undoes erases made in the *current*
    // session, so it intentionally doesn't carry over. Each placement's own
    // eraseHistory is different — it's restored below so "Reverse" and
    // vector-mode export both keep working correctly on erases from before
    // this reload too.
    undoStack.length = 0;
    for (const p of project.placements || []) {
      const isMask = p.type === "mask";
      const item = {
        id: "p" + Date.now() + Math.random().toString(36).slice(2, 7),
        type: p.type || "content",
        page: p.page,
        xPdf: p.xPdf, yPdf: p.yPdf, wPdf: p.wPdf, hPdf: p.hPdf,
        boundingBox: p.boundingBox,
        sourcePageIndex: p.sourcePageIndex,
        sourceBytes: isMask ? null : sourceBytesArr[p.sourceIndex],
        previewDataUrl: p.previewDataUrl,
        color: p.color,
        erased: !!p.erased,
        img: null,
        eraseHistory: [],
      };
      item.eraseHistory = (p.eraseHistory || []).map((e) => ({
        x: e.x, y: e.y, w: e.w, h: e.h, beforeDataUrl: e.beforeDataUrl, placementId: item.id,
      }));
      if (!isMask) item.img = preloadImage(item.previewDataUrl, item);
      placements.push(item);
    }
    selectedId = null;
    drawTargetOverlay();
    updatePlacementCount();
  }

  // Looks for a project payload we may have previously embedded inside a PDF's
  // catalog (see exportPdf below). Returns null for any PDF that doesn't have
  // one (including PDFs from other sources) — never throws.
  async function tryExtractEmbeddedProject(bytes) {
    try {
      const { PDFDocument, PDFName, PDFRawStream, decodePDFRawStream } = PDFLib;
      const doc = await PDFDocument.load(bytes.slice(), { updateMetadata: false });
      const ref = doc.catalog.get(PDFName.of(PROJECT_CATALOG_KEY));
      if (!ref) return null;
      const streamObj = doc.context.lookup(ref, PDFRawStream);
      if (!streamObj) return null;
      const decoded = decodePDFRawStream(streamObj).decode();
      const text = new TextDecoder("utf-8").decode(decoded);
      const project = JSON.parse(text);
      return project && project.type === PROJECT_TYPE ? project : null;
    } catch (err) {
      console.warn("no embedded project state found in this PDF:", err);
      return null;
    }
  }

  // Converts a "#rrggbb" colour string to the 0-1 float triple pdf-lib's
  // rgb() helper expects. Falls back to white for anything unparseable.
  function hexToRgb01(hex) {
    const m = /^#?([0-9a-f]{2})([0-9a-f]{2})([0-9a-f]{2})$/i.exec(hex || "#ffffff");
    if (!m) return { r: 1, g: 1, b: 1 };
    return { r: parseInt(m[1], 16) / 255, g: parseInt(m[2], 16) / 255, b: parseInt(m[3], 16) / 255 };
  }

  // ---------- true-vector clipping for erased placements ----------
  // Vector export normally re-embeds the *real* source PDF content for a
  // placement (embedPage/drawPage) so text stays selectable and lines stay
  // crisp. To make the eraser tools actually take effect in that mode too —
  // without flattening the whole placement into an image, which would lose
  // that editability — this traces exactly which pixels are *currently*
  // still erased (per eraseHistory entry, using each entry's own saved
  // "before" patch) into polygon outline(s), then those polygons are cut out
  // of the embedded vector content as a real PDF clipping path. The rest of
  // the placement keeps drawing as genuine, uneditable-as-image vector PDF
  // content — nothing gets rasterized.

  // Traces the outer boundary/boundaries of a binary pixel mask (1 = inside)
  // into one or more closed polygon loops, using "square tracing": every
  // pixel that borders a non-mask (or out-of-bounds) neighbour contributes a
  // unit edge along that border, then the edges are chained together at
  // shared corners into closed loops. Direction/winding doesn't matter since
  // the loops are only ever used with an even-odd clip rule.
  function traceMaskContours(mask, w, h) {
    const isIn = (x, y) => x >= 0 && x < w && y >= 0 && y < h && mask[y * w + x];
    const edges = [];
    for (let y = 0; y < h; y++) {
      for (let x = 0; x < w; x++) {
        if (!isIn(x, y)) continue;
        if (!isIn(x, y - 1)) edges.push([[x, y], [x + 1, y]]);
        if (!isIn(x, y + 1)) edges.push([[x, y + 1], [x + 1, y + 1]]);
        if (!isIn(x - 1, y)) edges.push([[x, y], [x, y + 1]]);
        if (!isIn(x + 1, y)) edges.push([[x + 1, y], [x + 1, y + 1]]);
      }
    }
    const key = (p) => p[0] + "," + p[1];
    const adj = new Map();
    function addAdj(p, edgeIdx) {
      const k = key(p);
      if (!adj.has(k)) adj.set(k, []);
      adj.get(k).push(edgeIdx);
    }
    edges.forEach((e, i) => { addAdj(e[0], i); addAdj(e[1], i); });

    const usedEdge = new Uint8Array(edges.length);
    const loops = [];
    for (let i = 0; i < edges.length; i++) {
      if (usedEdge[i]) continue;
      const loop = [];
      const startPoint = edges[i][0];
      let curPoint = startPoint;
      let curEdge = i;
      loop.push(curPoint);
      let guard = 0;
      while (guard++ < edges.length * 2 + 10) {
        usedEdge[curEdge] = 1;
        const e = edges[curEdge];
        const nextPoint = (e[0][0] === curPoint[0] && e[0][1] === curPoint[1]) ? e[1] : e[0];
        curPoint = nextPoint;
        if (curPoint[0] === startPoint[0] && curPoint[1] === startPoint[1]) break;
        loop.push(curPoint);
        const candidates = adj.get(key(curPoint)) || [];
        let found = -1;
        for (const c of candidates) { if (!usedEdge[c]) { found = c; break; } }
        if (found === -1) break; // dead end on a malformed/self-touching mask; keep what we traced
        curEdge = found;
      }
      if (loop.length >= 3) loops.push(loop);
    }
    return loops;
  }

  // Perpendicular distance from point p to the line through a-b, used by
  // Douglas-Peucker below.
  function perpDist(p, a, b) {
    const [x, y] = p, [x1, y1] = a, [x2, y2] = b;
    const dx = x2 - x1, dy = y2 - y1;
    const len2 = dx * dx + dy * dy;
    if (len2 === 0) return Math.hypot(x - x1, y - y1);
    const t = ((x - x1) * dx + (y - y1) * dy) / len2;
    return Math.hypot(x - (x1 + t * dx), y - (y1 + t * dy));
  }

  function douglasPeucker(points, epsilon) {
    if (points.length < 3) return points;
    let maxDist = 0, idx = 0;
    const a = points[0], b = points[points.length - 1];
    for (let i = 1; i < points.length - 1; i++) {
      const d = perpDist(points[i], a, b);
      if (d > maxDist) { maxDist = d; idx = i; }
    }
    if (maxDist > epsilon) {
      const left = douglasPeucker(points.slice(0, idx + 1), epsilon);
      const right = douglasPeucker(points.slice(idx), epsilon);
      return left.slice(0, -1).concat(right);
    }
    return [a, b];
  }

  // Grows a binary mask outward by `r` pixels in every direction (a simple
  // morphological dilation). Used right before tracing a clip hole: a hole
  // traced exactly at the boundary of the erased pixels can leave a
  // hairline of the original content still visible after export, because
  // the final PDF gets rasterized (by whatever viewer opens it) on its own
  // pixel grid, at its own resolution — independent of the one the erase
  // mask was captured at. A clip edge that lands within a fraction of a
  // device pixel of a thin line's edge can, depending on rounding, leave
  // that whole line un-clipped rather than partially clipped (confirmed by
  // testing against a real exported file: a 1px-wide erased line rendered
  // fully intact in Vector mode even though the hole polygon's boundary was
  // numerically correct). Padding the hole by a pixel in every direction
  // costs a barely-visible sliver of extra erased area but reliably removes
  // this class of rounding-edge remnant.
  function dilateMask(mask, w, h, r) {
    const out = new Uint8Array(w * h);
    for (let y = 0; y < h; y++) {
      for (let x = 0; x < w; x++) {
        if (!mask[y * w + x]) continue;
        const x0 = Math.max(0, x - r), x1 = Math.min(w - 1, x + r);
        const y0 = Math.max(0, y - r), y1 = Math.min(h - 1, y + r);
        for (let ny = y0; ny <= y1; ny++) {
          for (let nx = x0; nx <= x1; nx++) out[ny * w + nx] = 1;
        }
      }
    }
    return out;
  }

  // Removes points that are exactly collinear with both neighbours. Cheap,
  // always safe/lossless (can never change the polygon's shape or area),
  // and does most of the work for straight/axis-aligned runs — which a
  // pixel-grid trace is full of (e.g. a rectangle from "erase partial", or
  // the long straight sides of any traced blob).
  function collinearPass(loop) {
    if (loop.length < 3) return loop;
    const out = [];
    const n = loop.length;
    for (let i = 0; i < n; i++) {
      const prev = loop[(i - 1 + n) % n];
      const cur = loop[i];
      const next = loop[(i + 1) % n];
      const dx1 = cur[0] - prev[0], dy1 = cur[1] - prev[1];
      const dx2 = next[0] - cur[0], dy2 = next[1] - cur[1];
      if (dx1 * dy2 - dy1 * dx2 !== 0) out.push(cur);
    }
    return out.length >= 3 ? out : loop;
  }

  // A pixel-perfect trace of an erased region — especially one with
  // anti-aliased edges, like real rendered PDF content — walks in tiny
  // single-pixel zig-zag steps and can easily produce well over a thousand
  // points for one modest line. Some PDF viewers (Acrobat in particular)
  // can silently fail to apply / ignore a clipping path that's that large or
  // that jagged, even though more lenient renderers show it correctly, so
  // this simplifies further with real Douglas-Peucker. EPSILON_PX is in the
  // same raster pixel units as the trace itself, so it stays a tiny,
  // barely-noticeable tolerance regardless of placement size.
  //
  // Running Douglas-Peucker on a *closed* loop needs care: naively closing
  // it by appending the start point at the end and simplifying as one open
  // path (as an earlier version of this function did) uses that single
  // repeated point as BOTH ends of the reference line DP measures every
  // other point against. For a long, thin shape — exactly what an erased
  // line usually traces to — every point ends up "close enough" to that
  // degenerate zero-length reference and gets thrown away, collapsing the
  // whole polygon down to 2-3 points and a near-zero area. That silently
  // destroyed real erase holes (confirmed by testing against an actual
  // exported project) and is exactly the kind of bug that makes "I erased
  // it, but it's still in the exported file" happen. Splitting the loop into
  // two chains between two points that are genuinely far apart (here, index
  // 0 and its rough opposite by index) gives Douglas-Peucker a real
  // reference line on both halves instead.
  const CLIP_SIMPLIFY_EPSILON_PX = 1.2;
  function simplifyLoop(loop) {
    const reduced = collinearPass(loop);
    if (reduced.length < 5) return reduced;
    const n = reduced.length;
    const mid = Math.floor(n / 2);
    const chainA = reduced.slice(0, mid + 1);
    const chainB = reduced.slice(mid).concat([reduced[0]]);
    const simplifiedA = douglasPeucker(chainA, CLIP_SIMPLIFY_EPSILON_PX);
    const simplifiedB = douglasPeucker(chainB, CLIP_SIMPLIFY_EPSILON_PX);
    const merged = simplifiedA.slice(0, -1).concat(simplifiedB.slice(0, -1));
    return merged.length >= 3 ? merged : reduced;
  }

  function loadImageAsync(src) {
    return new Promise((resolve, reject) => {
      const img = new Image();
      img.onload = () => resolve(img);
      img.onerror = reject;
      img.src = src;
    });
  }

  // Figures out exactly which parts of a placement are *currently* still
  // erased (accounting for any partial "Reverse" restores) and returns that
  // as polygon loops in fractional placement-local coordinates (0..1 on
  // both axes, y measured bottom-up to match xPdf/yPdf/wPdf/hPdf). Each
  // eraseHistory entry's own beforeDataUrl patch always holds exactly the
  // pixels still hidden for that entry — Reverse zeroes out a pixel's alpha
  // there the moment it restores that pixel — so reading it directly stays
  // correct through any amount of partial undo/reverse without any extra
  // bookkeeping.
  //
  // Every entry's still-erased pixels are first OR'd together into ONE mask
  // covering the whole placement, and traced ONCE — rather than tracing each
  // entry separately and combining the separate polygons into one clip path.
  // Erasing something (especially "erase whole line" on a real, anti-aliased
  // line) very often takes several clicks, leaving several adjacent or
  // overlapping small entries. Tracing those independently and stacking the
  // resulting polygons as separate subpaths of one even-odd clip path is
  // unreliable in two different ways that were both confirmed to actually
  // happen: (1) two polygons that touch along a shared edge create a
  // degenerate "double edge" there under the even-odd rule, which can leave
  // a thin sliver of the supposedly-erased content still visible right along
  // that seam; (2) a single entry that's very thin (a 1-3px sliver, common
  // when a click only grabs part of an anti-aliased edge) can simplify away
  // to a zero-area line and vanish from the clip path entirely. Unioning
  // first avoids both — the merged shape is traced and simplified exactly
  // once, with no seams and (almost always) more width to work with.
  async function computeClipHolesForPlacement(pl) {
    const history = pl.eraseHistory || [];
    if (!history.length || !pl.rasterW || !pl.rasterH) return [];
    const W = pl.rasterW, H = pl.rasterH;
    const bigMask = new Uint8Array(W * H);
    let anyEntryLoaded = false;
    for (const entry of history) {
      try {
        const img = await loadImageAsync(entry.beforeDataUrl);
        const w = img.naturalWidth, h = img.naturalHeight;
        const canvas = document.createElement("canvas");
        canvas.width = w;
        canvas.height = h;
        const ctx = canvas.getContext("2d");
        ctx.drawImage(img, 0, 0);
        const data = ctx.getImageData(0, 0, w, h).data;
        for (let y = 0; y < h; y++) {
          for (let x = 0; x < w; x++) {
            if (data[(y * w + x) * 4 + 3] === 0) continue;
            const gx = x + entry.x, gy = y + entry.y;
            if (gx >= 0 && gx < W && gy >= 0 && gy < H) bigMask[gy * W + gx] = 1;
          }
        }
        anyEntryLoaded = true;
      } catch (err) {
        // Non-fatal: this one entry's pixels just don't get OR'd into the
        // mask (so that small area may show its original un-erased content
        // in vector mode), rather than failing the whole export.
        console.warn("could not rebuild an erase hole for vector export:", err);
      }
    }
    if (!anyEntryLoaded) return [];
    const paddedMask = dilateMask(bigMask, W, H, 1);
    const loops = traceMaskContours(paddedMask, W, H);
    const allLoops = [];
    for (const loop of loops) {
      const simplified = simplifyLoop(loop);
      const fracLoop = simplified.map(([px, py]) => [px / W, 1 - py / H]);
      if (fracLoop.length >= 3) allLoops.push(fracLoop);
    }
    return allLoops;
  }

  // ---------- export ----------
  async function exportPdf() {
    if (!tgtState.originalBytes) {
      alert("กรุณาอัปโหลด PDF ปลายทางก่อน");
      return;
    }
    downloadBtn.disabled = true;
    downloadBtn.textContent = "กำลังสร้างไฟล์...";
    const exportModeEl = document.querySelector('input[name="exportMode"]:checked');
    const exportMode = exportModeEl ? exportModeEl.value : "image";
    try {
      const {
        PDFDocument, PDFName, rgb,
        pushGraphicsState, popGraphicsState, moveTo, lineTo, closePath, clipEvenOdd, endPath,
      } = PDFLib;
      const pdfDoc = await PDFDocument.load(tgtState.originalBytes.slice());
      const pages = pdfDoc.getPages();

      // Draw "mask" placements first, on whichever page they belong to, so
      // they permanently cover the original PDF content underneath but still
      // sit below anything copied/pasted on top of them (drawn next, below).
      for (const pl of placements) {
        if (pl.type !== "mask") continue;
        const idx = pl.page - 1;
        if (idx < 0 || idx >= pages.length) continue;
        const { r, g, b } = hexToRgb01(pl.color);
        pages[idx].drawRectangle({ x: pl.xPdf, y: pl.yPdf, width: pl.wPdf, height: pl.hPdf, color: rgb(r, g, b) });
      }

      if (exportMode === "image") {
        // Embed each placement's raster snapshot as a plain Image XObject.
        // Nearly every PDF editor (Foxit, Acrobat, Preview, etc.) treats an
        // embedded image as one simple, self-contained object that can be
        // clicked, selected, moved, resized, or deleted with their normal
        // "edit objects/images" tool — the format most people expect when
        // they say "I want to edit this PDF afterwards".
        const imgCache = new Map();
        for (const pl of placements) {
          if (pl.type === "mask") continue; // already drawn above as a filled rectangle
          const idx = pl.page - 1;
          if (idx < 0 || idx >= pages.length) continue;
          let embedded = imgCache.get(pl.previewDataUrl);
          if (!embedded) {
            embedded = await pdfDoc.embedPng(dataUrlToUint8Array(pl.previewDataUrl));
            imgCache.set(pl.previewDataUrl, embedded);
          }
          pages[idx].drawImage(embedded, { x: pl.xPdf, y: pl.yPdf, width: pl.wPdf, height: pl.hPdf });
        }
      } else {
        // Cache one loaded PDFDocument per distinct source-bytes reference, so a
        // source PDF that multiple placements were copied from is only parsed once.
        const sourceDocCache = new Map();
        function getSourceDoc(bytes) {
          if (!sourceDocCache.has(bytes)) {
            sourceDocCache.set(bytes, PDFDocument.load(bytes.slice()));
          }
          return sourceDocCache.get(bytes);
        }

        for (const pl of placements) {
          if (pl.type === "mask") continue; // already drawn above as a filled rectangle
          const idx = pl.page - 1;
          if (idx < 0 || idx >= pages.length) continue;

          const sourceDoc = await getSourceDoc(pl.sourceBytes);
          const sourcePage = sourceDoc.getPage(pl.sourcePageIndex);
          // embedPage + a bounding box embeds the *actual* PDF content operators
          // from that region of the source page (vector paths, text, images it
          // already contained) as a reusable page object — nothing is flattened
          // into a raster image here. Note: most third-party PDF editors treat
          // this as one grouped object and won't let you edit pieces inside it.
          const embedded = await pdfDoc.embedPage(sourcePage, pl.boundingBox);
          const page = pages[idx];

          // If an eraser tool has touched this placement, cut the currently-
          // erased area(s) out of the embedded vector content with a real PDF
          // clipping path (evenodd: outer placement rect minus the erased-hole
          // polygon(s)) instead of rasterizing the whole placement. Text stays
          // selectable, lines stay crisp — only the exact erased region(s)
          // stop being drawn.
          const holes = await computeClipHolesForPlacement(pl);
          if (holes.length) {
            const toPageXY = (fx, fy) => [pl.xPdf + fx * pl.wPdf, pl.yPdf + fy * pl.hPdf];
            page.pushOperators(pushGraphicsState());
            const [ox0, oy0] = toPageXY(0, 0);
            const [ox1, oy1] = toPageXY(1, 1);
            page.pushOperators(moveTo(ox0, oy0), lineTo(ox1, oy0), lineTo(ox1, oy1), lineTo(ox0, oy1), closePath());
            for (const loop of holes) {
              const pts = loop.map(([fx, fy]) => toPageXY(fx, fy));
              const ops = [moveTo(pts[0][0], pts[0][1])];
              for (let i = 1; i < pts.length; i++) ops.push(lineTo(pts[i][0], pts[i][1]));
              ops.push(closePath());
              page.pushOperators(...ops);
            }
            page.pushOperators(clipEvenOdd(), endPath());
            page.drawPage(embedded, { x: pl.xPdf, y: pl.yPdf, width: pl.wPdf, height: pl.hPdf });
            page.pushOperators(popGraphicsState());
          } else {
            page.drawPage(embedded, { x: pl.xPdf, y: pl.yPdf, width: pl.wPdf, height: pl.hPdf });
          }
        }
      }

      // Also embed the full editable project state (pristine target + every
      // placement) invisibly inside this same PDF's catalog. Normal PDF
      // viewers just ignore the unknown entry, but if this exact output.pdf
      // is re-opened as the target in this tool later, we can detect it and
      // restore everything as movable/deletable items again — instead of a
      // flattened page nothing can be selected on. See tryExtractEmbeddedProject.
      try {
        const project = buildProjectObject();
        const stream = pdfDoc.context.flateStream(JSON.stringify(project), {
          Type: PDFName.of("Metadata"),
          Subtype: PDFName.of(PROJECT_CATALOG_KEY),
        });
        const streamRef = pdfDoc.context.register(stream);
        pdfDoc.catalog.set(PDFName.of(PROJECT_CATALOG_KEY), streamRef);
      } catch (embedErr) {
        // Non-fatal: worst case this particular output.pdf won't be resumable,
        // but the visible PDF content above is unaffected.
        console.warn("could not embed resumable project state:", embedErr);
      }

      const outBytes = await pdfDoc.save();
      const blob = new Blob([outBytes], { type: "application/pdf" });
      const url = URL.createObjectURL(blob);
      const a = document.createElement("a");
      a.href = url;
      a.download = "output.pdf";
      document.body.appendChild(a);
      a.click();
      a.remove();
      setTimeout(() => URL.revokeObjectURL(url), 5000);
    } catch (err) {
      console.error(err);
      alert("เกิดข้อผิดพลาดระหว่างสร้าง PDF: " + err.message);
    } finally {
      downloadBtn.disabled = false;
      downloadBtn.textContent = "⬇ ดาวน์โหลด PDF ผลลัพธ์";
    }
  }

  // ---------- project save / load ----------
  // "Save Project" writes the same state to a standalone .json file, which
  // is handy as a lighter-weight backup / for sharing the working session
  // without the flattened PDF content. Re-opening the exported PDF itself
  // (see tryExtractEmbeddedProject) works the same way and needs no separate
  // file at all.
  async function saveProject() {
    if (!tgtState.originalBytes) {
      alert("กรุณาอัปโหลด PDF ปลายทางก่อน");
      return;
    }
    const project = buildProjectObject();
    const blob = new Blob([JSON.stringify(project)], { type: "application/json" });
    const url = URL.createObjectURL(blob);
    const a = document.createElement("a");
    a.href = url;
    a.download = "project.pdftransfer.json";
    document.body.appendChild(a);
    a.click();
    a.remove();
    setTimeout(() => URL.revokeObjectURL(url), 5000);
  }

  async function loadProjectFile(file) {
    let project;
    try {
      project = JSON.parse(await file.text());
    } catch (err) {
      alert("ไฟล์โปรเจกต์ไม่ถูกต้อง: " + err.message);
      return;
    }
    if (!project || project.type !== PROJECT_TYPE) {
      alert("ไฟล์นี้ไม่ใช่ไฟล์โปรเจกต์ของเครื่องมือนี้");
      return;
    }
    await restoreProject(project);
  }

  // ---------- wire up top-level UI ----------
  srcFile.addEventListener("change", (e) => {
    if (e.target.files[0]) loadPdfFile(e.target.files[0], srcState, true);
  });
  tgtFile.addEventListener("change", async (e) => {
    const file = e.target.files[0];
    if (!file) return;
    const bytes = new Uint8Array(await file.arrayBuffer());
    // If this PDF was previously exported by this same tool, it carries its
    // own editable project state — recover it instead of treating the file
    // as a flat, non-editable page.
    const embeddedProject = await tryExtractEmbeddedProject(bytes);
    if (embeddedProject) {
      await restoreProject(embeddedProject);
      placementCount.textContent =
        `กู้คืนโปรเจกต์จากไฟล์นี้แล้ว — แก้ไข/ย้าย/ลบรายการที่เคยวางได้ตามปกติ (${placements.length} รายการ)`;
    } else {
      await loadPdfBytes(bytes, tgtState, false);
    }
  });

  srcPrev.addEventListener("click", () => {
    if (srcState.pageNum > 1) { srcState.pageNum--; renderSourcePage(); }
  });
  srcNext.addEventListener("click", () => {
    if (srcState.pdfDoc && srcState.pageNum < srcState.pdfDoc.numPages) { srcState.pageNum++; renderSourcePage(); }
  });
  tgtPrev.addEventListener("click", () => {
    if (tgtState.pageNum > 1) { tgtState.pageNum--; renderTargetPage(); }
  });
  tgtNext.addEventListener("click", () => {
    if (tgtState.pdfDoc && tgtState.pageNum < tgtState.pdfDoc.numPages) { tgtState.pageNum++; renderTargetPage(); }
  });

  copyBtn.addEventListener("click", copySelection);
  downloadBtn.addEventListener("click", exportPdf);

  const saveProjectBtn = document.getElementById("saveProjectBtn");
  const loadProjectFileInput = document.getElementById("loadProjectFile");
  if (saveProjectBtn) saveProjectBtn.addEventListener("click", saveProject);
  if (loadProjectFileInput) {
    loadProjectFileInput.addEventListener("change", (e) => {
      if (e.target.files[0]) loadProjectFile(e.target.files[0]);
      e.target.value = "";
    });
  }

  if (eraseBtn) {
    eraseBtn.disabled = true;
    eraseBtn.addEventListener("click", () => {
      erasing = !erasing;
      if (erasing) {
        erasingLine = false;
        reversing = false;
        masking = false;
        maskDrawing = false;
        curMaskRect = null;
        if (eraseLineBtn) eraseLineBtn.classList.remove("active");
        if (reverseBtn) reverseBtn.classList.remove("active");
        if (maskBtn) maskBtn.classList.remove("active");
      }
      eraseBtn.classList.toggle("active", erasing);
      curEraseRect = null;
      drawTargetOverlay();
    });
  }
  if (eraseLineBtn) {
    eraseLineBtn.disabled = true;
    eraseLineBtn.addEventListener("click", () => {
      erasingLine = !erasingLine;
      if (erasingLine) {
        erasing = false;
        reversing = false;
        masking = false;
        maskDrawing = false;
        curMaskRect = null;
        eraseDrawing = false;
        curEraseRect = null;
        if (eraseBtn) eraseBtn.classList.remove("active");
        if (reverseBtn) reverseBtn.classList.remove("active");
        if (maskBtn) maskBtn.classList.remove("active");
      }
      eraseLineBtn.classList.toggle("active", erasingLine);
      drawTargetOverlay();
    });
  }
  if (reverseBtn) {
    reverseBtn.disabled = true;
    reverseBtn.addEventListener("click", () => {
      reversing = !reversing;
      if (reversing) {
        erasing = false;
        erasingLine = false;
        masking = false;
        maskDrawing = false;
        curMaskRect = null;
        eraseDrawing = false;
        curEraseRect = null;
        if (eraseBtn) eraseBtn.classList.remove("active");
        if (eraseLineBtn) eraseLineBtn.classList.remove("active");
        if (maskBtn) maskBtn.classList.remove("active");
      }
      reverseBtn.classList.toggle("active", reversing);
      drawTargetOverlay();
    });
  }

  if (undoBtn) {
    undoBtn.disabled = true;
    undoBtn.addEventListener("click", undoLastErase);
  }

  if (maskBtn) {
    maskBtn.disabled = true;
    maskBtn.addEventListener("click", () => {
      masking = !masking;
      if (masking) {
        erasing = false;
        erasingLine = false;
        reversing = false;
        eraseDrawing = false;
        curEraseRect = null;
        if (eraseBtn) eraseBtn.classList.remove("active");
        if (eraseLineBtn) eraseLineBtn.classList.remove("active");
        if (reverseBtn) reverseBtn.classList.remove("active");
      }
      maskBtn.classList.toggle("active", masking);
      maskDrawing = false;
      curMaskRect = null;
      drawTargetOverlay();
    });
  }

  // Ctrl+Z / Cmd+Z: undo the most recently applied erase, on any placement.
  // Registered on window + capture phase, and matches on e.code as well as
  // e.key, so it still fires reliably across keyboard layouts/browsers even
  // if some other element or extension would otherwise intercept it first.
  // The "↶ Undo" button above does the exact same thing with a plain click,
  // as a guaranteed fallback if this shortcut doesn't fire for any reason.
  window.addEventListener("keydown", (e) => {
    const key = (e.key || "").toLowerCase();
    const isUndo = (e.ctrlKey || e.metaKey) && !e.shiftKey && !e.altKey && (key === "z" || e.code === "KeyZ");
    if (isUndo) {
      e.preventDefault();
      undoLastErase();
    }
  }, true);
})();
