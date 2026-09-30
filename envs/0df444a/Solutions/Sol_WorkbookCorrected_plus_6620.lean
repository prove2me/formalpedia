-- Prove2me | solution 1 for WorkbookCorrected.plus_6620
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-29T14:47:39.62392+00:00
-- url     : https://prove2.me/submissions/5291daf5-b520-4a4a-b7d4-8c1d3c0882fd

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

theorem solution : (0:ℚ) + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 = (0:ℚ) := by
  norm_num
