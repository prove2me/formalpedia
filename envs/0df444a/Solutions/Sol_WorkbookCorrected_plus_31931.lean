-- Prove2me | solution 1 for WorkbookCorrected.plus_31931
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-06T20:56:38.07742+00:00
-- url     : https://prove2.me/submissions/f285ae0d-92bb-4022-b4c5-8ce284d901a9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem solution : 10 * 8 * 6 * 4 / (Nat.factorial 4) = 80 := by
  decide
