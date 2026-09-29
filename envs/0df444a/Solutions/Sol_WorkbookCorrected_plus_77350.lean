-- Prove2me | solution 1 for WorkbookCorrected.plus_77350
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T08:43:45.25181+00:00
-- url     : https://prove2.me/submissions/c89d0b85-b4dd-4bfc-bbec-57493d3cd376

import Mathlib.Tactic.NormNum

theorem solution : (6 : ℚ) / 21 * 8 / 15 + (8 : ℚ) / 21 * 6 / 13 = 64 / 195 := by
  norm_num
