-- Prove2me | solution 1 for WorkbookCorrected.plus_73773
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T08:30:03.682567+00:00
-- url     : https://prove2.me/submissions/29aecb68-1b36-4637-8bbf-862da51de9d4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem solution : Nat.factorial 6 / Nat.factorial 2 = 720 / 2 := by
  decide
