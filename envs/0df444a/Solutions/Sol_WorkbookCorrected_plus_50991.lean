-- Prove2me | solution 1 for WorkbookCorrected.plus_50991
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-23T13:08:44.369465+00:00
-- url     : https://prove2.me/submissions/c97ed853-cbb0-49e8-9f98-cc1709164873

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem solution : (Nat.factorial 5) = 5 * 4 * 3 * 2 * 1 := by
  decide
