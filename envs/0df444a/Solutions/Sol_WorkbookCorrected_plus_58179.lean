-- Prove2me | solution 1 for WorkbookCorrected.plus_58179
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T08:43:33.2371+00:00
-- url     : https://prove2.me/submissions/c03fa06f-b631-4b51-998e-990229df1e68

import Mathlib.Data.Nat.Factorial.Basic

theorem solution : Nat.factorial 5 / (Nat.factorial 2 * Nat.factorial 2) = 30 := by
  decide
