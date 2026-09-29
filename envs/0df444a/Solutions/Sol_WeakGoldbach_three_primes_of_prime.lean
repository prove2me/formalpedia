-- Prove2me | solution 1 for WeakGoldbach.three_primes_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T21:27:49.230716+00:00
-- url     : https://prove2.me/submissions/d81980cf-846f-4895-b4b3-778c421a5b74

import Mathlib

set_option autoImplicit false

theorem solution (p : ℕ) (hp : Nat.Prime p) :
    ∃ s : Multiset ℕ, s.card ≤ 3 ∧ (∀ q ∈ s, Nat.Prime q) ∧ s.sum = p :=
  ⟨{p}, by simp, by simpa using hp, by simp⟩
