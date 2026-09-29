-- Prove2me | solution 1 for WorkbookCorrected.plus_58052
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T08:43:32.300768+00:00
-- url     : https://prove2.me/submissions/b5e7a8a0-a5d2-4e88-a303-e66aac775bcf

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem solution : Nat.factorial 8 - (4 * Nat.factorial 7 - 2 * Nat.factorial 6) = 21600 := by
  decide
