-- Prove2me | solution 1 for WorkbookCorrected.plus_54975
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T08:43:44.076702+00:00
-- url     : https://prove2.me/submissions/663c8566-e9ee-4ef4-9975-4877047d8453

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum

theorem solution : (1000 : ℕ) + (1000 - 9) + (1000 - 99) + (1000 - 999) = 2893 := by
  norm_num
