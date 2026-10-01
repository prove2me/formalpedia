-- Prove2me | solution 1 for WorkbookCorrected.plus_45361
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-01T07:10:03.892122+00:00
-- url     : https://prove2.me/submissions/fedb9af9-112c-4add-b157-44b258951c91

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem solution : ((Nat.factorial 15))/((Nat.factorial 9) * (Nat.factorial 6)) = 5005 := by
  decide
