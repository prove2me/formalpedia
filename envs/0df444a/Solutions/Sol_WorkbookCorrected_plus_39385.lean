-- Prove2me | solution 1 for WorkbookCorrected.plus_39385
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-06T20:57:25.861155+00:00
-- url     : https://prove2.me/submissions/cb017d95-e7ae-4585-96ba-99dc2e87cc5a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem solution : (Nat.factorial 8) / ((Nat.factorial 2) * (Nat.factorial 2) * (Nat.factorial 2) * (Nat.factorial 2)) = 2520 := by
  decide
