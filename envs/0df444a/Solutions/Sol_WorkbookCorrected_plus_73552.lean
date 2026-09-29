-- Prove2me | solution 1 for WorkbookCorrected.plus_73552
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T08:18:55.531341+00:00
-- url     : https://prove2.me/submissions/644ebb6f-013f-4bf2-8a63-930aba7e56ce

import Mathlib.Data.Nat.Factorial.Basic

theorem solution : Nat.factorial 10 / (Nat.factorial 4 * Nat.factorial 3 * Nat.factorial 2 * Nat.factorial 1) = 12600 := by
  decide
