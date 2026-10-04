-- Prove2me | solution 1 for WorkbookCorrected.plus_6012
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-03T09:27:38.868007+00:00
-- url     : https://prove2.me/submissions/8e8afac8-3d23-4441-a6f9-f178c65a14f9

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

theorem solution : (5/8:ℚ) = (5/8:ℚ) := by
  norm_num
