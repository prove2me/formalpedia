-- Prove2me | solution 1 for WorkbookCorrected.plus_72890
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T08:14:35.575796+00:00
-- url     : https://prove2.me/submissions/d5178950-8cc3-42a3-a4c9-fb88ade9c106

import Mathlib.Data.Nat.Factorial.Basic

theorem solution : Nat.factorial 15 % 1000 = 0 := by
  decide
