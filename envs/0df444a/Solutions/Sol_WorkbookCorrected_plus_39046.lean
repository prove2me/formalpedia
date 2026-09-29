-- Prove2me | solution 1 for WorkbookCorrected.plus_39046
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T08:47:50.481365+00:00
-- url     : https://prove2.me/submissions/f00b7120-455e-4f9f-b4b8-1d1170dc122e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem solution : Nat.factorial 9 / (Nat.factorial 2 * Nat.factorial 2 * Nat.factorial 4) = 3780 := by
  decide
