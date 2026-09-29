-- Prove2me | solution 1 for WorkbookCorrected.plus_13125
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-23T13:27:51.63686+00:00
-- url     : https://prove2.me/submissions/a1d8d69f-ba8e-440c-ab08-a5376e5a39e4

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

theorem solution : ((1680:ℚ) / (1680 + 448)) = ((15:ℚ) / 19) := by
  norm_num
