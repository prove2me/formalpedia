-- Prove2me | solution 1 for WorkbookCorrected.plus_24145
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T11:45:47.335045+00:00
-- url     : https://prove2.me/submissions/b054cbcd-2f90-49ff-9886-962ed3b0d615

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem solution : (Nat.factorial 7)/((Nat.factorial 2)*(Nat.factorial 2)) = 1260 := by
  decide
