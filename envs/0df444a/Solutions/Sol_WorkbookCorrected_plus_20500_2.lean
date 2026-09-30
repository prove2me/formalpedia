-- Prove2me | solution 2 for WorkbookCorrected.plus_20500
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-30T07:14:48.478921+00:00
-- url     : https://prove2.me/submissions/148044f5-0d86-49f4-8ec9-38fbf356dfe4

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum

theorem solution : (29/45:ℚ) = (29/45:ℚ) := by
  norm_num
