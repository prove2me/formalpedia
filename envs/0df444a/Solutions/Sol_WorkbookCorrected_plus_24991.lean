-- Prove2me | solution 1 for WorkbookCorrected.plus_24991
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T08:47:46.13872+00:00
-- url     : https://prove2.me/submissions/bd655cf0-0f5c-41df-8ae4-ee0f06ac341d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem solution : Nat.factorial 1 + Nat.factorial 2 + Nat.factorial 3 + Nat.factorial 4 + Nat.factorial 5 = 153 := by
  decide
