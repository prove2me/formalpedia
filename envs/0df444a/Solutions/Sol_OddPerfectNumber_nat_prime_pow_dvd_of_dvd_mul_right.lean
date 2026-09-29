-- Prove2me | solution 1 for OddPerfectNumber.nat_prime_pow_dvd_of_dvd_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T01:46:14.977174+00:00
-- url     : https://prove2.me/submissions/750e15a4-e4e7-4cd7-828e-2996547c0403

import Mathlib

theorem solution (p a b n : Nat)
    (hp : p.Prime)
    (hnot : ¬ p ∣ b)
    (hdiv : p ^ n ∣ a * b) :
    p ^ n ∣ a := by
  exact hp.prime.pow_dvd_of_dvd_mul_right n hnot hdiv
