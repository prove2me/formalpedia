-- Prove2me | solution 1 for WorkbookCorrected.plus_64443
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T08:43:30.350441+00:00
-- url     : https://prove2.me/submissions/2ef5ca74-8b70-4f7e-9807-e22b33adccd9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem solution : Nat.factorial 10 / (Nat.factorial 2) ^ 3 - 3 * Nat.factorial 9 / (Nat.factorial 2) ^ 2 + 3 * Nat.factorial 8 / Nat.factorial 2 - Nat.factorial 7 = 236880 := by
  decide
