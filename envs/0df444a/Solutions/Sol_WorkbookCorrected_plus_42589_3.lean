-- Prove2me | solution 3 for WorkbookCorrected.plus_42589
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-03T09:07:22.187933+00:00
-- url     : https://prove2.me/submissions/cad6f39f-18e6-4f5c-b7e8-182b19e1f00f

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

theorem solution : (5/22:ℚ) = (5/22:ℚ) := by
  ring
