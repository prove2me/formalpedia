-- Prove2me | solution 1 for WorkbookCorrected.plus_48564
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T08:47:49.022864+00:00
-- url     : https://prove2.me/submissions/c187cfc4-acf7-40f6-b6e3-11c858e89469

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem solution : Nat.factorial 10 / (Nat.factorial 2 * Nat.factorial 8) = 45 := by
  decide
