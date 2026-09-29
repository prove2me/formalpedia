-- Prove2me | solution 1 for WorkbookCorrected.plus_62975
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T08:53:05.578345+00:00
-- url     : https://prove2.me/submissions/4904b5e5-2251-4b37-84c2-39e6127940b6

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem solution : (Nat.choose 9 4) * ((Nat.factorial 5) / ((Nat.factorial 2) * (Nat.factorial 2))) = (Nat.factorial 9) / ((Nat.factorial 2) * (Nat.factorial 2) * (Nat.factorial 4)) := by
  decide
