-- Prove2me | solution 1 for WorkbookCorrected.plus_70458
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T08:18:56.77628+00:00
-- url     : https://prove2.me/submissions/24205478-c784-46e0-adb6-198a50a0eaf3

import Mathlib.Data.Nat.Factorial.Basic

theorem solution : Nat.factorial 7 / (Nat.factorial 3 * Nat.factorial 3) = 140 := by
  decide
