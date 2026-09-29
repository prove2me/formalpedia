-- Prove2me | solution 2 for WorkbookCorrected.plus_35143
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T11:51:30.234149+00:00
-- url     : https://prove2.me/submissions/fdf3607f-7f82-4123-a736-d1649be7926f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem solution : (Nat.factorial 12)/(((Nat.factorial 3)*(Nat.factorial 9))) = 220 := by
  decide
