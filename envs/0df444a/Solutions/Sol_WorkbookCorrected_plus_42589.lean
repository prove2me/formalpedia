-- Prove2me | solution 1 for WorkbookCorrected.plus_42589
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-03T08:55:10.507126+00:00
-- url     : https://prove2.me/submissions/14bf7390-d4a6-4310-8e6a-58df709aadab

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

theorem solution : (5/22:ℚ) = (5/22:ℚ) := by
  norm_num
