-- Prove2me | solution 1 for WorkbookCorrected.plus_14815
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T11:50:33.998388+00:00
-- url     : https://prove2.me/submissions/96d3af51-01d3-4bf8-a2b0-48f950f4b9c6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem solution : ((Nat.factorial 6))/((Nat.factorial 2)*(Nat.factorial 3)) = 60 := by
  decide
