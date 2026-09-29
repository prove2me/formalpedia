-- Prove2me | solution 1 for WorkbookCorrected.plus_60818
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-23T13:23:16.064873+00:00
-- url     : https://prove2.me/submissions/74932e47-6bea-4c4b-a321-d41364077671

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem solution : (Nat.factorial 10) / ((Nat.factorial 4) * (Nat.factorial 6)) * ((Nat.factorial 6) / ((Nat.factorial 3) * (Nat.factorial 3))) * ((Nat.factorial 3) / ((Nat.factorial 2) * (Nat.factorial 1))) * ((Nat.factorial 1) / ((Nat.factorial 1) * (Nat.factorial 0))) = 12600 := by
  decide
