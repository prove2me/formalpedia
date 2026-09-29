-- Prove2me | solution 1 for WorkbookCorrected.plus_14131
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T11:52:51.741586+00:00
-- url     : https://prove2.me/submissions/a6c1bbe8-23c5-4ff9-8e16-42a249d70b15

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem solution : (Nat.factorial 5) = 5 * 4 * 3 * 2 * 1 := by
  decide
