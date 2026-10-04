-- Prove2me | solution 1 for OddPerfectNumber.Kernel.five_two_prime_index_primes_dvd_sigma
-- status  : ACCEPTED   (prove)
-- author  : @os0xcom
-- created : 2026-10-03T16:04:26.864682+00:00
-- url     : https://prove2.me/submissions/6ec61e4d-7dc5-4f63-b49c-83acae7297e1

import Mathlib

theorem solution (p m d1 q r : Nat)
    (h2 : (∑ d ∈ (m ^ 2).divisors, d) = p ^ 5 * (d1 ^ 2 * (q * r))) :
    (q ∣ ∑ d ∈ (m ^ 2).divisors, d) ∧ (r ∣ ∑ d ∈ (m ^ 2).divisors, d) := by
  have hq0 : q ∣ q * r := by simpa [Nat.mul_comm] using dvd_mul_left q r
  have hr0 : r ∣ q * r := dvd_mul_left r q
  have hq : q ∣ p ^ 5 * (d1 ^ 2 * (q * r)) :=
    dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hq0 _) _
  have hr : r ∣ p ^ 5 * (d1 ^ 2 * (q * r)) :=
    dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hr0 _) _
  constructor
  · rw [h2]; exact hq
  · rw [h2]; exact hr
