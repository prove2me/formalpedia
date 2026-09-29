-- Prove2me | solution 1 for WorkbookCorrected.plus_29982
-- status  : ACCEPTED   (prove)
-- author  : @Rizwan G Mir
-- created : 2026-09-24T19:28:26.36678+00:00
-- url     : https://prove2.me/submissions/4a5f60b6-9973-4109-a5ba-de56c37f4b7e

import Mathlib

theorem solution (n r : ℕ) (h₁ : n ≥ r) : Nat.choose n r = Nat.choose n (n - r) :=
  (Nat.choose_symm h₁).symm
