-- Prove2me | solution 1 for WorkbookCorrected.plus_77334
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T08:25:20.932905+00:00
-- url     : https://prove2.me/submissions/90b93623-4d5c-4bf3-8da4-e82ba7f3d1a1

import Mathlib.Data.Nat.Totient

theorem solution (n : ℕ) (h : n = 15) : Nat.totient n = 8 := by
  subst h
  decide
