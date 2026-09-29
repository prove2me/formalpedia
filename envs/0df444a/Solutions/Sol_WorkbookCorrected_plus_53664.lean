-- Prove2me | solution 1 for WorkbookCorrected.plus_53664
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T08:30:04.636384+00:00
-- url     : https://prove2.me/submissions/402ccd75-01e5-453e-9b6f-ed318fb2fd84

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem solution : Nat.factorial 10 / (60 * 60 * 24) = 42 := by
  decide
