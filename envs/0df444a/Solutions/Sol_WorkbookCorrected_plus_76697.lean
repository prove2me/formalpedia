-- Prove2me | solution 1 for WorkbookCorrected.plus_76697
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-01T06:41:23.264275+00:00
-- url     : https://prove2.me/submissions/aac35d5b-a449-40d8-955a-7ff0279d25a4

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum

theorem solution : (1/100:ℚ) = (1/100:ℚ) := by
  norm_num
