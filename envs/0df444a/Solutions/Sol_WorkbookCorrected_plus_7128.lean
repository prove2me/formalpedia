-- Prove2me | solution 1 for WorkbookCorrected.plus_7128
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T11:56:40.25411+00:00
-- url     : https://prove2.me/submissions/f4031780-b8d8-4af8-a74a-22db6576670a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem solution : (Nat.factorial 9) / (5 * 4 * 3 * 4 * 3 * 2 * 3 * 2 * 1) = 42 := by
  decide
