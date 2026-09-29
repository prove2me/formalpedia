-- Prove2me | solution 1 for OddPerfectNumber.k_one_diophantine_m_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T06:03:38.85533+00:00
-- url     : https://prove2.me/submissions/46a03e42-893d-4367-bb05-88d2faf52540

import Mathlib

theorem solution (p m : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hpm : ¬ p ∣ m) (hm_odd : Odd m)
    (hm1 : m = 1)
    (heq : (1 + p) * (∑ d ∈ (m ^ 2).divisors, d) = 2 * (p * m ^ 2)) : False := by
  subst hm1
  simp only [one_pow, Nat.divisors_one, Finset.sum_singleton] at heq
  have hp2 : 2 ≤ p := hp.two_le
  omega
