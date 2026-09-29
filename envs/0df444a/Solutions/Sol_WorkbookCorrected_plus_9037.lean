-- Prove2me | solution 1 for WorkbookCorrected.plus_9037
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T11:57:17.886497+00:00
-- url     : https://prove2.me/submissions/b0f671f5-f11a-49fa-8479-946b0334ba23

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem solution : (Nat.factorial 10) / ((Nat.factorial 8) * (Nat.factorial 2)) * ((Nat.factorial 4) / ((Nat.factorial 2) * (Nat.factorial 2))) * ((Nat.factorial 4) / ((Nat.factorial 2) * (Nat.factorial 2))) = 1620 := by
  decide
