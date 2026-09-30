-- Prove2me | solution 1 for WorkbookCorrected.plus_55641
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-29T12:50:58.052231+00:00
-- url     : https://prove2.me/submissions/56c786a6-4d65-4c27-a5f9-9b626a9fe805

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem solution : ((Nat.factorial 7) * (Nat.factorial 4) * 70) = ((Nat.factorial 7) * (Nat.factorial 4) * (Nat.choose (4+5-1) (5-1))) := by
  decide
