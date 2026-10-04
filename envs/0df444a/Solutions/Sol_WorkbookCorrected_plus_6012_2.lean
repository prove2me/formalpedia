-- Prove2me | solution 2 for WorkbookCorrected.plus_6012
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-03T09:35:45.413663+00:00
-- url     : https://prove2.me/submissions/539d5481-04c8-4bea-b95c-3b4a059b20e0

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

theorem solution : (5/8:ℚ) = (5/8:ℚ) := by
  simp
