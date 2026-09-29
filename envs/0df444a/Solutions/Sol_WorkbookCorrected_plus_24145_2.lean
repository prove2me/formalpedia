-- Prove2me | solution 2 for WorkbookCorrected.plus_24145
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T11:55:31.504975+00:00
-- url     : https://prove2.me/submissions/f5240da7-f553-48a0-94e6-85c4c111c2a2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem solution : (Nat.factorial 7)/((Nat.factorial 2)*(Nat.factorial 2)) = 1260 := by
  decide
