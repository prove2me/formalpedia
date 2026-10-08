-- Prove2me | solution 1 for OddPerfectNumber.Kernel.d1_prime_dvd_sigma_of_second_dris
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T14:26:59.120286+00:00
-- url     : https://prove2.me/submissions/3beaf024-a15a-4e85-83ed-e48c1f158e27

import Mathlib

theorem solution (p m d1 q r : Nat) (hq : q.Prime)
    (hr : r.Prime)
    (h2 : (∑ d ∈ (m ^ 2).divisors, d) = p ^ 5 * (d1 ^ 2 * (q * r)))
    (t : Nat) (ht : t.Prime) (htd : Dvd.dvd t d1) :
    Dvd.dvd t (∑ d ∈ (m ^ 2).divisors, d) := by
  rw [h2]
  exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (dvd_pow htd two_ne_zero) _) _
