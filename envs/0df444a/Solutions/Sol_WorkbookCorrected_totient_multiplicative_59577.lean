-- Prove2me | solution 1 for WorkbookCorrected.totient_multiplicative_59577
-- status  : ACCEPTED   (prove)
-- author  : @Rizwan G Mir
-- created : 2026-09-24T19:50:55.501137+00:00
-- url     : https://prove2.me/submissions/5979625f-2980-40fa-b1e1-fbf806f25f42

import Mathlib

theorem solution : ∀ m n : ℕ, m ≠ 0 → n ≠ 0 → Nat.Coprime m n → Nat.totient (m * n) = Nat.totient m * Nat.totient n := by
  intro m n _ _ hcop
  exact Nat.totient_mul hcop
