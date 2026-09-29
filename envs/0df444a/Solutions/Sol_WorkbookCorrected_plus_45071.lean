-- Prove2me | solution 1 for WorkbookCorrected.plus_45071
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T08:52:53.110321+00:00
-- url     : https://prove2.me/submissions/3d60fa87-91df-4e0d-a9c5-7de6b3fb421d

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem solution : (Nat.factorial 3) * (Nat.choose 4 2) * (Nat.choose 6 2) = 540 := by
  decide
