-- Prove2me | solution 2 for WorkbookCorrected.plus_24602
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T11:47:25.367272+00:00
-- url     : https://prove2.me/submissions/c208520d-efed-470d-ba18-c8fb85a138d7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem solution : 12 * 10 * 8 * 6 * 4 / (Nat.factorial 5) = 192 := by
  decide
