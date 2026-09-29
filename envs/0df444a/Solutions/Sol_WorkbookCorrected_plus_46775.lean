-- Prove2me | solution 1 for WorkbookCorrected.plus_46775
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-23T13:11:41.596367+00:00
-- url     : https://prove2.me/submissions/289e9c20-043b-4e07-8c83-8fba5eb75399

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem solution : 3 * ((Nat.factorial 4) / ((Nat.factorial 2) * (Nat.factorial 1) * (Nat.factorial 1))) = 36 := by
  decide
