-- Prove2me | solution 1 for WorkbookCorrected.plus_31265
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-03T09:11:25.413016+00:00
-- url     : https://prove2.me/submissions/81d6e6b1-6dbc-455e-81d8-23432c0b7414

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

theorem solution : (81/1000:ℚ) = (81/1000:ℚ) := by
  norm_num
