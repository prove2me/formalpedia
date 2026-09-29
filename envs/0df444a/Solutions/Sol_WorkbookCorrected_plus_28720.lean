-- Prove2me | solution 1 for WorkbookCorrected.plus_28720
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T11:57:37.070036+00:00
-- url     : https://prove2.me/submissions/d8e8cddd-1152-402e-88a7-4b95b9aa9ce8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem solution : (Nat.factorial 11) / ((Nat.factorial 7) * (Nat.factorial 4)) + (Nat.factorial 9) / ((Nat.factorial 5) * (Nat.factorial 4)) + (Nat.factorial 7) / ((Nat.factorial 3) * (Nat.factorial 4)) + (Nat.factorial 5) / ((Nat.factorial 1) * (Nat.factorial 4)) = 496 := by
  decide
