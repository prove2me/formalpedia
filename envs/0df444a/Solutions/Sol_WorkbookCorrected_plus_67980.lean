-- Prove2me | solution 1 for WorkbookCorrected.plus_67980
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T08:14:35.01049+00:00
-- url     : https://prove2.me/submissions/cb5d60f1-ff08-4a30-9157-7a7f39e92f1d

import Mathlib.Data.Nat.Factorial.Basic

theorem solution : Nat.factorial 8 / (Nat.factorial 2 * Nat.factorial 2) = 10080 := by
  decide
