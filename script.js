const boardElement = document.querySelector("#board");
const scoreElement = document.querySelector("#score");
const comboElement = document.querySelector("#combo");
const movesElement = document.querySelector("#moves");
const timerElement = document.querySelector("#timer");
const statusElement = document.querySelector("#status");
const restartButton = document.querySelector("#restartButton");
const hintButton = document.querySelector("#hintButton");
const cellTemplate = document.querySelector("#cellTemplate");
const fireworksCanvas = document.querySelector("#fireworksCanvas");
const resultOverlay = document.querySelector("#resultOverlay");
const timerBox = timerElement.closest(".timer-box");

const rowCount = 10;
const columnCount = 8;
const minValue = 1;
const maxValue = 9;
const initialTimeLimit = 120;
const generationAttempts = 140;
const assignmentAttempts = 56;
const blockShapes = [
  { height: 1, width: 2, weight: 10 },
  { height: 2, width: 1, weight: 10 },
  { height: 1, width: 3, weight: 10 },
  { height: 3, width: 1, weight: 10 },
  { height: 2, width: 2, weight: 9 },
  { height: 1, width: 4, weight: 5 },
  { height: 4, width: 1, weight: 5 }
];

const blockValueOptionsCache = new Map();

let board = [];
let selectedCells = [];
let dragAnchor = null;
let isDragging = false;
let activePointerId = null;
let score = 0;
let combo = 0;
let secondsLeft = initialTimeLimit;
let timerId = null;
let gameState = "idle";
let fireworksParticles = [];
let fireworksAnimationId = null;
let fireworkTimers = [];

function createStartingBoard() {
  board = createSolvableBoard();
}

function createSolvableBoard() {
  let bestCandidate = null;
  let bestScore = Number.NEGATIVE_INFINITY;

  for (let attempt = 0; attempt < generationAttempts; attempt += 1) {
    const layout = generateBlockLayout();
    if (!layout) {
      continue;
    }

    const targetCounts = createTargetDigitCounts();
    const candidate = assignBoardForLayout(layout, targetCounts);
    if (!candidate) {
      continue;
    }

    const scoreValue = evaluateCandidateDifficulty(candidate);
    if (scoreValue > bestScore) {
      bestScore = scoreValue;
      bestCandidate = candidate;
    }
  }

  if (bestCandidate) {
    return bestCandidate.board;
  }

  const fallbackCandidate = assignBoardForLayout(createFallbackLayout(), createTargetDigitCounts());
  if (fallbackCandidate) {
    return fallbackCandidate.board;
  }

  return createGuaranteedFallbackBoard();
}

function createTargetDigitCounts() {
  const counts = [0, 11, 11, 10, 9, 8, 7, 7, 8, 9];

  for (let step = 0; step < 4; step += 1) {
    const donor = 1 + Math.floor(Math.random() * maxValue);
    const receiver = 1 + Math.floor(Math.random() * maxValue);

    if (donor === receiver || counts[donor] <= 3 || counts[receiver] >= 14) {
      continue;
    }

    counts[donor] -= 1;
    counts[receiver] += 1;
  }

  return counts;
}

function generateBlockLayout() {
  const occupied = Array.from({ length: rowCount }, () =>
    Array.from({ length: columnCount }, () => false)
  );

  return fillBlocksRecursively(occupied, []);
}

function fillBlocksRecursively(occupied, blocks) {
  const nextCell = findFirstEmptyCell(occupied);
  if (!nextCell) {
    return blocks.map((block) => ({ ...block }));
  }

  const shapes = getOrderedShapes();
  for (const shape of shapes) {
    if (!canPlaceBlock(occupied, nextCell.row, nextCell.column, shape)) {
      continue;
    }

    markBlock(occupied, nextCell.row, nextCell.column, shape, true);
    blocks.push({
      row: nextCell.row,
      column: nextCell.column,
      height: shape.height,
      width: shape.width
    });

    const result = fillBlocksRecursively(occupied, blocks);
    if (result) {
      return result;
    }

    blocks.pop();
    markBlock(occupied, nextCell.row, nextCell.column, shape, false);
  }

  return null;
}

function getOrderedShapes() {
  return [...blockShapes].sort((left, right) => {
    const leftScore = left.weight + Math.random() * 3;
    const rightScore = right.weight + Math.random() * 3;
    return rightScore - leftScore;
  });
}

function canPlaceBlock(occupied, startRow, startColumn, shape) {
  const endRow = startRow + shape.height;
  const endColumn = startColumn + shape.width;

  if (endRow > rowCount || endColumn > columnCount) {
    return false;
  }

  for (let row = startRow; row < endRow; row += 1) {
    for (let column = startColumn; column < endColumn; column += 1) {
      if (occupied[row][column]) {
        return false;
      }
    }
  }

  return true;
}

function markBlock(occupied, startRow, startColumn, shape, value) {
  for (let row = startRow; row < startRow + shape.height; row += 1) {
    for (let column = startColumn; column < startColumn + shape.width; column += 1) {
      occupied[row][column] = value;
    }
  }
}

function findFirstEmptyCell(occupied) {
  for (let row = 0; row < rowCount; row += 1) {
    for (let column = 0; column < columnCount; column += 1) {
      if (!occupied[row][column]) {
        return { row, column };
      }
    }
  }

  return null;
}

function assignBoardForLayout(layout, targetCounts) {
  const sortedLayout = [...layout].sort((left, right) => {
    const leftArea = left.height * left.width;
    const rightArea = right.height * right.width;
    return rightArea - leftArea;
  });

  let bestCandidate = null;
  let bestDeviation = Number.POSITIVE_INFINITY;

  for (let attempt = 0; attempt < assignmentAttempts; attempt += 1) {
    const nextBoard = Array.from({ length: rowCount }, () =>
      Array.from({ length: columnCount }, () => null)
    );
    const digitCounts = Array.from({ length: maxValue + 1 }, () => 0);
    const remainingCounts = [...targetCounts];
    const blocks = [];
    let failed = false;

    for (const block of shuffle(sortedLayout)) {
      const cells = collectBlockCells(block);
      const values = chooseValuesForBlock(cells.length, digitCounts, remainingCounts);

      if (!values) {
        failed = true;
        break;
      }

      cells.forEach((cell, index) => {
        const value = values[index];
        nextBoard[cell.row][cell.column] = value;
        digitCounts[value] += 1;
        remainingCounts[value] -= 1;
      });

      blocks.push({
        row: block.row,
        column: block.column,
        height: block.height,
        width: block.width,
        cells,
        centerRow: block.row + (block.height - 1) / 2,
        centerColumn: block.column + (block.width - 1) / 2
      });
    }

    if (failed) {
      continue;
    }

    const deviation = measureDistributionDeviation(remainingCounts);
    const candidate = {
      board: nextBoard,
      blocks,
      digitCounts,
      targetCounts,
      distributionDeviation: deviation
    };

    if (deviation < bestDeviation) {
      bestDeviation = deviation;
      bestCandidate = candidate;
    }

    if (deviation === 0) {
      return candidate;
    }
  }

  return bestCandidate;
}

function collectBlockCells(block) {
  const cells = [];

  for (let row = block.row; row < block.row + block.height; row += 1) {
    for (let column = block.column; column < block.column + block.width; column += 1) {
      cells.push({ row, column });
    }
  }

  return cells;
}

function chooseValuesForBlock(cellCount, digitCounts, remainingCounts) {
  const options = getBlockValueOptions(cellCount);
  const validOptions = options.filter((option) => canUseOption(option, remainingCounts));
  const candidateOptions = validOptions.length > 0 ? validOptions : options;

  if (candidateOptions.length === 0) {
    return null;
  }

  const scoredOptions = candidateOptions
    .map((option) => ({
      option,
      score: scoreValueOption(option, digitCounts, remainingCounts)
    }))
    .sort((left, right) => right.score - left.score);

  const pickedPool = scoredOptions.slice(0, Math.min(6, scoredOptions.length));
  const chosen = pickedPool[Math.floor(Math.random() * pickedPool.length)].option;

  return shuffle(chosen);
}

function getBlockValueOptions(cellCount) {
  if (!blockValueOptionsCache.has(cellCount)) {
    const options = [];
    buildBlockValueOptions(cellCount, 10, 1, [], options);
    blockValueOptionsCache.set(cellCount, options);
  }

  return blockValueOptionsCache.get(cellCount);
}

function buildBlockValueOptions(cellCount, remainingSum, minDigit, current, options) {
  if (cellCount === 0) {
    if (remainingSum === 0) {
      options.push([...current]);
    }
    return;
  }

  const maxDigit = Math.min(9, remainingSum - (cellCount - 1));
  for (let digit = minDigit; digit <= maxDigit; digit += 1) {
    const nextRemaining = remainingSum - digit;
    const minPossibleRest = digit * (cellCount - 1);
    const maxPossibleRest = 9 * (cellCount - 1);

    if (cellCount > 1 && (nextRemaining < minPossibleRest || nextRemaining > maxPossibleRest)) {
      continue;
    }

    current.push(digit);
    buildBlockValueOptions(cellCount - 1, nextRemaining, digit, current, options);
    current.pop();
  }
}

function canUseOption(option, remainingCounts) {
  const required = Array.from({ length: maxValue + 1 }, () => 0);
  option.forEach((digit) => {
    required[digit] += 1;
  });

  for (let digit = minValue; digit <= maxValue; digit += 1) {
    if (required[digit] > remainingCounts[digit]) {
      return false;
    }
  }

  return true;
}

function scoreValueOption(option, digitCounts, remainingCounts) {
  const targetCount = (rowCount * columnCount) / 9;
  let scoreValue = 0;

  option.forEach((digit) => {
    const deficit = Math.max(0, targetCount - digitCounts[digit]);
    const remainPressure = remainingCounts[digit] * 3.2;
    const repeatPenalty = digitCounts[digit] * 0.85;
    const highDigitBonus = digit >= 6 ? digit * 0.7 : digit * 0.18;
    scoreValue += deficit * 2.3 + remainPressure + highDigitBonus - repeatPenalty;
  });

  scoreValue += new Set(option).size * 1.7;
  scoreValue += Math.max(...option) * 0.45;
  scoreValue += option.filter((digit) => digit === 9).length * 18;
  scoreValue += option.filter((digit) => digit === 8).length * 6;

  if (option.length === 2) {
    scoreValue += option.includes(9) ? 2 : -8;
  } else if (option.length === 3) {
    scoreValue += 3.8;
  } else if (option.length === 4) {
    scoreValue += 8.5;
  } else if (option.length >= 5) {
    scoreValue += 5.2;
  }

  return scoreValue;
}

function measureDistributionDeviation(remainingCounts) {
  let deviation = 0;

  for (let digit = minValue; digit <= maxValue; digit += 1) {
    deviation += Math.abs(remainingCounts[digit]);
  }

  return deviation;
}

function createFallbackLayout() {
  const layout = [];

  for (let row = 0; row < rowCount; row += 1) {
    for (let column = 0; column < columnCount; column += 2) {
      layout.push({
        row,
        column,
        height: 1,
        width: 2
      });
    }
  }

  return layout;
}

function createGuaranteedFallbackBoard() {
  const boardState = Array.from({ length: rowCount }, () =>
    Array.from({ length: columnCount }, () => null)
  );
  const pairOptions = shuffle([
    [1, 9],
    [2, 8],
    [3, 7],
    [4, 6],
    [5, 5]
  ]);

  let pairIndex = 0;

  for (let row = 0; row < rowCount; row += 1) {
    for (let column = 0; column < columnCount; column += 2) {
      const pair = [...pairOptions[pairIndex % pairOptions.length]];
      if (Math.random() < 0.5) {
        pair.reverse();
      }

      boardState[row][column] = pair[0];
      boardState[row][column + 1] = pair[1];
      pairIndex += 1;
    }
  }

  return boardState;
}

function shuffle(items) {
  const nextItems = [...items];

  for (let index = nextItems.length - 1; index > 0; index -= 1) {
    const swapIndex = Math.floor(Math.random() * (index + 1));
    [nextItems[index], nextItems[swapIndex]] = [nextItems[swapIndex], nextItems[index]];
  }

  return nextItems;
}

function evaluateCandidateDifficulty(candidate) {
  const validSelections = findAllValidSelectionsForBoard(candidate.board);
  const layoutScore = evaluateLayoutDifficulty(candidate.blocks);
  const extraSelections = Math.max(0, validSelections.length - candidate.blocks.length);
  const adjacentPairCount = countAdjacentPairSelections(candidate.board);
  const pairSelectionCount = countSelectionsByCellCount(validSelections, 2);
  const largeSelectionCount = countSelectionsAtLeast(validSelections, 4);
  const minimumNineTarget = 2;
  const nineShortagePenalty = Math.max(0, minimumNineTarget - candidate.digitCounts[9]) * 90;
  const highDigitPresenceBonus = candidate.digitCounts[9] * 52 + candidate.digitCounts[8] * 10;
  const routeDistance = calculateRouteDistanceScore(candidate.blocks);
  const spreadScore = calculateSpreadScore(candidate.blocks);
  const averageArea = candidate.blocks.reduce(
    (sum, block) => sum + block.height * block.width,
    0
  ) / candidate.blocks.length;
  const distributionPenalty = candidate.distributionDeviation * 2400;

  return (
    layoutScore +
    candidate.blocks.length * 9 -
    distributionPenalty -
    extraSelections * 46 -
    adjacentPairCount * 110 -
    pairSelectionCount * 52 +
    largeSelectionCount * 10 +
    highDigitPresenceBonus +
    -nineShortagePenalty +
    routeDistance * 18 +
    spreadScore * 20 -
    averageArea * 2 +
    Math.random()
  );
}

function evaluateLayoutDifficulty(blocks) {
  let scoreValue = 0;
  const shapeKinds = new Set();

  blocks.forEach((block) => {
    const area = block.height * block.width;
    shapeKinds.add(`${block.height}x${block.width}`);

    if (area === 2) {
      scoreValue += 8;
    } else if (area === 3) {
      scoreValue += 14;
    } else if (area === 4) {
      scoreValue += 18;
    } else {
      scoreValue -= area * 2;
    }
  });

  scoreValue += blocks.length * 4;
  scoreValue += shapeKinds.size * 4;

  return scoreValue;
}

function countAdjacentPairSelections(boardState) {
  let count = 0;

  for (let row = 0; row < rowCount; row += 1) {
    for (let column = 0; column < columnCount; column += 1) {
      const value = boardState[row][column];
      if (value === null) {
        continue;
      }

      if (column + 1 < columnCount && boardState[row][column + 1] !== null) {
        if (value + boardState[row][column + 1] === 10) {
          count += 1;
        }
      }

      if (row + 1 < rowCount && boardState[row + 1][column] !== null) {
        if (value + boardState[row + 1][column] === 10) {
          count += 1;
        }
      }
    }
  }

  return count;
}

function countSelectionsByCellCount(selections, targetCellCount) {
  return selections.reduce((count, selection) => {
    return count + (selection.length === targetCellCount ? 1 : 0);
  }, 0);
}

function countSelectionsAtLeast(selections, minCellCount) {
  return selections.reduce((count, selection) => {
    return count + (selection.length >= minCellCount ? 1 : 0);
  }, 0);
}

function calculateRouteDistanceScore(blocks) {
  if (blocks.length < 2) {
    return 0;
  }

  const remaining = [...blocks];
  const route = [remaining.shift()];

  while (remaining.length > 0) {
    const current = route[route.length - 1];
    let farthestIndex = 0;
    let farthestDistance = -1;

    remaining.forEach((block, index) => {
      const distance =
        Math.abs(block.centerRow - current.centerRow) +
        Math.abs(block.centerColumn - current.centerColumn);

      if (distance > farthestDistance) {
        farthestDistance = distance;
        farthestIndex = index;
      }
    });

    route.push(remaining.splice(farthestIndex, 1)[0]);
  }

  let total = 0;
  for (let index = 1; index < route.length; index += 1) {
    total +=
      Math.abs(route[index].centerRow - route[index - 1].centerRow) +
      Math.abs(route[index].centerColumn - route[index - 1].centerColumn);
  }

  return total / (route.length - 1);
}

function calculateSpreadScore(blocks) {
  let total = 0;

  blocks.forEach((block, index) => {
    let nearest = Number.POSITIVE_INFINITY;

    blocks.forEach((otherBlock, otherIndex) => {
      if (index === otherIndex) {
        return;
      }

      const distance =
        Math.abs(block.centerRow - otherBlock.centerRow) +
        Math.abs(block.centerColumn - otherBlock.centerColumn);
      nearest = Math.min(nearest, distance);
    });

    total += Number.isFinite(nearest) ? nearest : 0;
  });

  return total / Math.max(1, blocks.length);
}

function renderBoard() {
  boardElement.innerHTML = "";
  boardElement.style.gridTemplateColumns = `repeat(${columnCount}, minmax(0, 1fr))`;

  board.forEach((row, rowIndex) => {
    row.forEach((value, columnIndex) => {
      const cell = cellTemplate.content.firstElementChild.cloneNode(true);
      const isEmpty = value === null;

      cell.dataset.row = String(rowIndex);
      cell.dataset.column = String(columnIndex);

      if (isEmpty) {
        cell.textContent = "";
        cell.dataset.value = "empty";
        cell.classList.add("empty");
        cell.setAttribute("aria-label", `第 ${rowIndex + 1} 行，第 ${columnIndex + 1} 列，空白`);
      } else {
        cell.textContent = String(value);
        cell.dataset.value = String(value);
        cell.setAttribute(
          "aria-label",
          `第 ${rowIndex + 1} 行，第 ${columnIndex + 1} 列，数字 ${value}`
        );
      }

      if (isCellSelected(rowIndex, columnIndex)) {
        cell.classList.add("selected");
      }

      if (dragAnchor && dragAnchor.row === rowIndex && dragAnchor.column === columnIndex) {
        cell.classList.add("anchor");
      }

      if (gameState !== "playing") {
        cell.disabled = true;
      }

      boardElement.appendChild(cell);
    });
  });

  updateStats();
}

function updateStats() {
  scoreElement.textContent = String(score);
  comboElement.textContent = String(combo);
  movesElement.textContent = String(findAllValidSelections().length);
  timerElement.textContent = formatTime(secondsLeft);
  timerBox.classList.toggle("warning", secondsLeft <= 30);
}

function formatTime(totalSeconds) {
  const minutes = String(Math.floor(totalSeconds / 60)).padStart(2, "0");
  const seconds = String(totalSeconds % 60).padStart(2, "0");
  return `${minutes}:${seconds}`;
}

function startTimer() {
  stopTimer();
  timerId = window.setInterval(() => {
    if (gameState !== "playing") {
      return;
    }

    secondsLeft = Math.max(0, secondsLeft - 1);
    updateStats();

    if (secondsLeft === 0) {
      endGame("timeup");
    }
  }, 1000);
}

function stopTimer() {
  if (timerId !== null) {
    window.clearInterval(timerId);
    timerId = null;
  }
}

function onBoardPointerDown(event) {
  if (gameState !== "playing" || !event.isPrimary) {
    return;
  }

  if (event.pointerType === "mouse" && event.button !== 0) {
    return;
  }

  const targetCell = getCellFromEventTarget(event.target);
  if (!targetCell) {
    return;
  }

  const value = board[targetCell.row][targetCell.column];
  if (value === null) {
    return;
  }

  event.preventDefault();
  activePointerId = event.pointerId;
  isDragging = true;
  dragAnchor = targetCell;
  selectedCells = [targetCell];
  if (typeof boardElement.setPointerCapture === "function") {
    boardElement.setPointerCapture(event.pointerId);
  }
  setStatus(`当前选区和：${value}。按住左键继续拖动，松开后完成框选。`);
  renderBoard();
}

function onBoardPointerMove(event) {
  if (!isDragging || gameState !== "playing" || event.pointerId !== activePointerId) {
    return;
  }

  event.preventDefault();
  const targetCell = getClosestCellFromPoint(event.clientX, event.clientY);
  if (!targetCell) {
    return;
  }

  updateSelection(targetCell.row, targetCell.column);
}

function updateSelection(row, column) {
  if (!dragAnchor) {
    return;
  }

  selectedCells = getCellsInRectangle(dragAnchor, { row, column });
  const total = getSelectionSum(selectedCells);

  if (total > 10) {
    setStatus(`当前选区和：${total}，已经超过 10，松开后本次选择会取消。`);
  } else if (total === 10) {
    setStatus(`当前选区和：${total}。松开左键即可消除。`);
  } else {
    setStatus(`当前选区和：${total}。按住左键继续拖动。`);
  }

  renderBoard();
}

function finalizeSelection() {
  if (!isDragging || gameState !== "playing") {
    return;
  }

  isDragging = false;
  activePointerId = null;

  if (selectedCells.length === 0) {
    clearSelection();
    setStatus("本次没有选中任何数字。");
    renderBoard();
    return;
  }

  const total = getSelectionSum(selectedCells);
  if (total !== 10) {
    combo = 0;
    clearSelection();
    setStatus(`当前选区和为 ${total}，不等于 10，本次不消除。`);
    renderBoard();
    return;
  }

  const eliminatedCount = selectedCells.length;
  eliminateCells(selectedCells);
  combo += 1;
  score += 10 + Math.max(0, eliminatedCount - 2) * 4 + (combo - 1) * 5;
  clearSelection();

  const remainingCells = countRemainingCells();
  if (remainingCells === 0) {
    renderBoard();
    endGame("win");
    return;
  }

  const remainingMoves = findAllValidSelections().length;
  if (remainingMoves === 0) {
    setStatus("消除成功，但当前已经没有可继续凑 10 的矩形选区了。");
  } else {
    setStatus(`消除成功，选区总和为 10。当前连击 ${combo}。`);
  }

  renderBoard();
}

function releaseBoardPointer(pointerId) {
  if (typeof boardElement.releasePointerCapture !== "function") {
    return;
  }

  try {
    boardElement.releasePointerCapture(pointerId);
  } catch (error) {
    // Pointer capture may already be released on some browsers.
  }
}

function onBoardPointerUp(event) {
  if (event.pointerId !== activePointerId) {
    return;
  }

  releaseBoardPointer(event.pointerId);
  finalizeSelection();
}

function onBoardPointerCancel(event) {
  if (event.pointerId !== activePointerId) {
    return;
  }

  releaseBoardPointer(event.pointerId);
  isDragging = false;
  activePointerId = null;
  clearSelection();
  setStatus("Selection cancelled. Drag again to retry.");
  renderBoard();
}

function onBoardLostPointerCapture(event) {
  if (event.pointerId !== activePointerId || !isDragging) {
    return;
  }

  finalizeSelection();
}

function eliminateCells(cells) {
  cells.forEach(({ row, column }) => {
    board[row][column] = null;
  });
}

function findAllValidSelections() {
  return findAllValidSelectionsForBoard(board);
}

function findAllValidSelectionsForBoard(boardState) {
  const results = [];
  const uniqueAreas = new Set();

  for (let startRow = 0; startRow < rowCount; startRow += 1) {
    for (let startColumn = 0; startColumn < columnCount; startColumn += 1) {
      for (let endRow = startRow; endRow < rowCount; endRow += 1) {
        for (let endColumn = startColumn; endColumn < columnCount; endColumn += 1) {
          const cells = getCellsInRectangle(
            { row: startRow, column: startColumn },
            { row: endRow, column: endColumn },
            boardState
          );

          if (cells.length === 0 || getSelectionSum(cells, boardState) !== 10) {
            continue;
          }

          const key = buildAreaKey(cells);
          if (uniqueAreas.has(key)) {
            continue;
          }

          uniqueAreas.add(key);
          results.push(cells);
        }
      }
    }
  }

  return results;
}

function buildAreaKey(cells) {
  return cells.map((cell) => `${cell.row},${cell.column}`).join("|");
}

function getCellsInRectangle(firstCell, secondCell, boardState = board) {
  const startRow = Math.min(firstCell.row, secondCell.row);
  const endRow = Math.max(firstCell.row, secondCell.row);
  const startColumn = Math.min(firstCell.column, secondCell.column);
  const endColumn = Math.max(firstCell.column, secondCell.column);
  const cells = [];

  for (let row = startRow; row <= endRow; row += 1) {
    for (let column = startColumn; column <= endColumn; column += 1) {
      if (boardState[row][column] !== null) {
        cells.push({ row, column });
      }
    }
  }

  return cells;
}

function getSelectionSum(cells, boardState = board) {
  return cells.reduce((total, cell) => total + boardState[cell.row][cell.column], 0);
}

function isCellSelected(row, column) {
  return selectedCells.some((cell) => cell.row === row && cell.column === column);
}

function getCellFromEventTarget(target) {
  const cell = target.closest(".cell");
  if (!cell || !boardElement.contains(cell)) {
    return null;
  }

  return {
    row: Number(cell.dataset.row),
    column: Number(cell.dataset.column)
  };
}

function getCellFromPoint(clientX, clientY) {
  const element = document.elementFromPoint(clientX, clientY);
  if (!element) {
    return null;
  }

  return getCellFromEventTarget(element);
}

function getClosestCellFromPoint(clientX, clientY) {
  const directCell = getCellFromPoint(clientX, clientY);
  if (directCell) {
    return directCell;
  }

  const rect = boardElement.getBoundingClientRect();
  const insideBoard =
    clientX >= rect.left &&
    clientX <= rect.right &&
    clientY >= rect.top &&
    clientY <= rect.bottom;

  if (!insideBoard) {
    const clampedX = Math.min(Math.max(clientX, rect.left + 1), rect.right - 1);
    const clampedY = Math.min(Math.max(clientY, rect.top + 1), rect.bottom - 1);
    return getCellFromPoint(clampedX, clampedY);
  }

  return null;
}

function clearSelection() {
  selectedCells = [];
  dragAnchor = null;
  activePointerId = null;
}

function countRemainingCells() {
  let count = 0;

  for (let row = 0; row < rowCount; row += 1) {
    for (let column = 0; column < columnCount; column += 1) {
      if (board[row][column] !== null) {
        count += 1;
      }
    }
  }

  return count;
}

function showHint() {
  if (gameState !== "playing") {
    return;
  }

  const selection = findAllValidSelections()[0];
  if (!selection) {
    setStatus("当前没有可提示的矩形选区，直接重新开局更快。");
    return;
  }

  selection.forEach((cell) => {
    const button = document.querySelector(
      `.cell[data-row="${cell.row}"][data-column="${cell.column}"]`
    );
    if (button) {
      button.classList.remove("hint");
      void button.offsetWidth;
      button.classList.add("hint");
    }
  });

  setStatus("提示：按住左键拖动，框住高亮区域，松开即可消除。");
}

function setStatus(message) {
  statusElement.textContent = message;
}

function showOverlay(content, type = "") {
  resultOverlay.innerHTML = content;
  resultOverlay.className = "result-overlay show";
  if (type) {
    resultOverlay.classList.add(type);
  }
}

function hideOverlay() {
  resultOverlay.innerHTML = "";
  resultOverlay.className = "result-overlay";
}

function resizeFireworksCanvas() {
  const rect = boardElement.getBoundingClientRect();
  fireworksCanvas.width = Math.max(1, Math.floor(rect.width * window.devicePixelRatio));
  fireworksCanvas.height = Math.max(1, Math.floor(rect.height * window.devicePixelRatio));
  fireworksCanvas.style.width = `${rect.width}px`;
  fireworksCanvas.style.height = `${rect.height}px`;
}

function launchFireworks() {
  resizeFireworksCanvas();
  fireworksCanvas.classList.add("active");
  fireworksParticles = [];
  clearFireworkTimers();

  for (let round = 0; round < 4; round += 1) {
    const timerId = window.setTimeout(() => {
      fireworkTimers = fireworkTimers.filter((id) => id !== timerId);
      spawnFireworkRound(round);
      animateFireworks();
    }, round * 420);

    fireworkTimers.push(timerId);
  }
}

function spawnFireworkRound(roundIndex) {
  const width = fireworksCanvas.width;
  const height = fireworksCanvas.height;
  const burstCount = 4 + roundIndex * 2;
  const particleCount = 32 + roundIndex * 10;

  for (let burstIndex = 0; burstIndex < burstCount; burstIndex += 1) {
    const centerX = width * (0.08 + Math.random() * 0.84);
    const centerY = height * (0.08 + Math.random() * 0.52);
    const colorBase = Math.floor(Math.random() * 360);

    for (let particleIndex = 0; particleIndex < particleCount; particleIndex += 1) {
      const angle = (Math.PI * 2 * particleIndex) / particleCount;
      const speed = 2.3 + Math.random() * (4.1 + roundIndex * 0.9);
      fireworksParticles.push({
        x: centerX,
        y: centerY,
        vx: Math.cos(angle) * speed,
        vy: Math.sin(angle) * speed,
        life: 58 + Math.random() * 28 + roundIndex * 6,
        size: 1.8 + Math.random() * 2.8,
        color: `hsl(${(colorBase + particleIndex * 5) % 360} 96% 64%)`
      });
    }
  }
}

function animateFireworks() {
  if (fireworksAnimationId !== null) {
    return;
  }

  const context = fireworksCanvas.getContext("2d");
  if (!context) {
    return;
  }

  const frame = () => {
    context.clearRect(0, 0, fireworksCanvas.width, fireworksCanvas.height);

    fireworksParticles = fireworksParticles.filter((particle) => particle.life > 0);
    fireworksParticles.forEach((particle) => {
      particle.x += particle.vx;
      particle.y += particle.vy;
      particle.vy += 0.045;
      particle.life -= 1;

      context.globalAlpha = Math.max(0, particle.life / 90);
      context.fillStyle = particle.color;
      context.beginPath();
      context.arc(particle.x, particle.y, particle.size, 0, Math.PI * 2);
      context.fill();
    });

    context.globalAlpha = 1;

    if (fireworksParticles.length > 0 || fireworkTimers.length > 0) {
      fireworksAnimationId = window.requestAnimationFrame(frame);
    } else {
      fireworksCanvas.classList.remove("active");
      fireworksAnimationId = null;
    }
  };

  fireworksAnimationId = window.requestAnimationFrame(frame);
}

function clearFireworkTimers() {
  while (fireworkTimers.length > 0) {
    window.clearTimeout(fireworkTimers.pop());
  }
}

function cancelFireworks() {
  if (fireworksAnimationId !== null) {
    window.cancelAnimationFrame(fireworksAnimationId);
    fireworksAnimationId = null;
  }

  clearFireworkTimers();
  fireworksParticles = [];

  const context = fireworksCanvas.getContext("2d");
  if (context) {
    context.clearRect(0, 0, fireworksCanvas.width, fireworksCanvas.height);
  }

  fireworksCanvas.classList.remove("active");
}

function endGame(reason) {
  gameState = reason;
  isDragging = false;
  clearSelection();
  stopTimer();
  renderBoard();

  if (reason === "win") {
    setStatus("你已经清空整个棋盘，通关成功。");
    showOverlay(
      '<div class="victory-stack"><div class="victory-title">通关</div><div class="victory-subtitle">最终得分：' +
        score +
        "</div></div>",
      "success"
    );
    launchFireworks();
    return;
  }

  if (reason === "timeup") {
    setStatus("时间到，本局结束。");
    showOverlay(
      '<div class="victory-stack"><div class="victory-subtitle">时间到</div><div class="victory-subtitle">最终得分：' +
        score +
        "</div></div>"
    );
  }
}

function restartGame() {
  score = 0;
  combo = 0;
  secondsLeft = initialTimeLimit;
  gameState = "playing";
  isDragging = false;
  clearSelection();
  hideOverlay();
  cancelFireworks();
  createStartingBoard();
  setStatus("新的一局开始了，按住左键拖动拉出矩形选区，把总和凑到 10。");
  renderBoard();
  startTimer();
}

boardElement.addEventListener("pointerdown", onBoardPointerDown);
boardElement.addEventListener("pointermove", onBoardPointerMove);
boardElement.addEventListener("pointerup", onBoardPointerUp);
boardElement.addEventListener("pointercancel", onBoardPointerCancel);
boardElement.addEventListener("lostpointercapture", onBoardLostPointerCapture);
window.addEventListener("resize", resizeFireworksCanvas);
restartButton.addEventListener("click", restartGame);
hintButton.addEventListener("click", showHint);

restartGame();
