-- Prove2me | solution 2 for WorkbookCorrected.plus_42589
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-03T09:03:17.856003+00:00
-- url     : https://prove2.me/submissions/1d89c811-be17-4912-be4e-b6f3a191228d

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

theorem solution : (5/22:ℚ) = (5/22:ℚ) := by
  simp
