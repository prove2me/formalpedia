-- Prove2me | solution 1 for OddPerfectNumber.sigma_mul_perfect
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T11:05:30.099231+00:00
-- url     : https://prove2.me/submissions/04d6484b-867d-4363-99e9-277046e2658c

import Mathlib

-- Coprime divisor sums multiply (Nat.Coprime.sum_divisors_mul), so the
-- packaged equation is exactly sum_divisors = 2 * val.
theorem solution (a b sa sb : Nat) (hcop : Nat.Coprime a b)
    (hpos : 0 < a * b)
    (ha : (∑ x ∈ a.divisors, x) = sa)
    (hb : (∑ x ∈ b.divisors, x) = sb)
    (h : sa * sb = 2 * (a * b)) :
    Nat.Perfect (a * b) := by
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul hpos,
    hcop.sum_divisors_mul, ha, hb, h]
