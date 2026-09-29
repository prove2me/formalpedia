-- Prove2me | solution 1 for WorkbookCorrected.plus_78618
-- status  : ACCEPTED   (prove)
-- author  : @Rizwan G Mir
-- created : 2026-09-24T19:36:25.556046+00:00
-- url     : https://prove2.me/submissions/f7b3c800-8770-4410-88a7-8792329c1ffd

import Mathlib

theorem solution (n r : ℕ) (h₁ : r ≤ n) (h₂ : n - r ≤ n) : Nat.choose n r = Nat.choose n (n - r) :=
  (Nat.choose_symm h₁).symm
