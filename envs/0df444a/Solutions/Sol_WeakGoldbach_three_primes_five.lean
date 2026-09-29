-- Prove2me | solution 1 for WeakGoldbach.three_primes_five
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T21:27:49.2812+00:00
-- url     : https://prove2.me/submissions/c23eb1bc-cbf7-4b4d-8f74-13dcfcde66b0

import Mathlib

set_option autoImplicit false

theorem solution :
    ∃ s : Multiset ℕ, s.card ≤ 3 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = 5 :=
  ⟨{5}, by simp, by simp; norm_num, by simp⟩
