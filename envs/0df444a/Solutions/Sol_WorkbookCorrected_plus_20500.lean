-- Prove2me | solution 1 for WorkbookCorrected.plus_20500
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-30T07:09:44.98+00:00
-- url     : https://prove2.me/submissions/1652bea9-0720-4a12-8b2e-2d49215435aa

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum

theorem solution : (29/45:ℚ) = (29/45:ℚ) := by
  norm_num
