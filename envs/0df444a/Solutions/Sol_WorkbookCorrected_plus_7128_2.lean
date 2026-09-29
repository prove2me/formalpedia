-- Prove2me | solution 2 for WorkbookCorrected.plus_7128
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-23T13:00:02.325544+00:00
-- url     : https://prove2.me/submissions/26a265ce-df1c-45a7-aac4-3ff948a6abc5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem solution : (Nat.factorial 9) / (5 * 4 * 3 * 4 * 3 * 2 * 3 * 2 * 1) = 42 := by
  decide
