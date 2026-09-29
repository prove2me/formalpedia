-- Prove2me | solution 1 for WeakGoldbach.three_primes_three
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T21:27:49.315073+00:00
-- url     : https://prove2.me/submissions/b9e9a36b-d89c-4ffd-b5c4-c956ffb5c31f

import Mathlib

set_option autoImplicit false

theorem solution :
    ∃ s : Multiset ℕ, s.card ≤ 3 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = 3 :=
  ⟨{3}, by simp, by simp; norm_num, by simp⟩
