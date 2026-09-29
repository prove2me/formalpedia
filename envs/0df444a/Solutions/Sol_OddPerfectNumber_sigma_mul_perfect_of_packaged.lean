-- Prove2me | solution 1 for OddPerfectNumber.sigma_mul_perfect_of_packaged
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T10:21:37.752545+00:00
-- url     : https://prove2.me/submissions/0ad05165-59e4-41ec-8361-5460d35ef5af

import Mathlib

-- STAGED direct proof: multiplicativity + packaged rewrite + criterion.
-- Hypothesis names are 5+ letters: short names (ha/hb/h) with
-- parenthesized types trip the canonical concatenated-identifier guard
-- (remote raw_target_parse_error on the v1 statement; see regression test).
theorem solution (a b sa sb : Nat) (hcop : Nat.Coprime a b)
    (hpos : 0 < a * b)
    (hsiga : (∑ x ∈ a.divisors, x) = sa)
    (hsigb : (∑ x ∈ b.divisors, x) = sb)
    (hpack : sa * sb = 2 * (a * b)) :
    Nat.Perfect (a * b) := by
  have hN : (∑ x ∈ (a * b).divisors, x) = 2 * (a * b) := by
    rw [hcop.sum_divisors_mul, hsiga, hsigb]
    exact hpack
  exact (Nat.perfect_iff_sum_divisors_eq_two_mul hpos).mpr hN
