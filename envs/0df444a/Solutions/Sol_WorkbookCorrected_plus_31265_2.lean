-- Prove2me | solution 2 for WorkbookCorrected.plus_31265
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-03T09:19:31.914151+00:00
-- url     : https://prove2.me/submissions/00ba1c0d-f7bb-461f-92ec-d31bb0039303

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

theorem solution : (81/1000:ℚ) = (81/1000:ℚ) := by
  simp
