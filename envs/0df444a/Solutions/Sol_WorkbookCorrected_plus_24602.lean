-- Prove2me | solution 1 for WorkbookCorrected.plus_24602
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T11:44:56.731611+00:00
-- url     : https://prove2.me/submissions/f010942c-fda2-41e1-a133-3d47491739dc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem solution : 12 * 10 * 8 * 6 * 4 / (Nat.factorial 5) = 192 := by
  decide
