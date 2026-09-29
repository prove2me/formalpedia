-- Prove2me | solution 1 for WorkbookCorrected.plus_37901
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T11:53:29.298+00:00
-- url     : https://prove2.me/submissions/57c1423b-22b8-4a2e-9adf-3a6d1dd60be2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem solution : ((Nat.factorial 10)/((Nat.factorial 2)*(Nat.factorial 3)))-((Nat.factorial 9)/((Nat.factorial 2)*(Nat.factorial 2))) = 211680 := by
  decide
