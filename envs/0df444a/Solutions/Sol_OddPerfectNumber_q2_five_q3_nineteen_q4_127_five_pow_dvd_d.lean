-- Prove2me | solution 1 for OddPerfectNumber.q2_five_q3_nineteen_q4_127_five_pow_dvd_d
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T06:29:07.723645+00:00
-- url     : https://prove2.me/submissions/2eaed399-a0d0-43f6-bc95-f9cd5dc2f007

import Mathlib
import Theorems.Thm_OddPerfectNumber_nat_prime_pow_dvd_of_dvd_mul_right

theorem solution (m d : Nat)
    (hprod : m ^ 2 = 64 * d)
    (hpow : 5 ^ 6 ∣ m ^ 2) :
    5 ^ 6 ∣ d := by
  have hdiv : 5 ^ 6 ∣ d * 64 := by
    rw [Nat.mul_comm d 64]
    simpa [hprod] using hpow
  exact OddPerfectNumber.nat_prime_pow_dvd_of_dvd_mul_right
    5 d 64 6 (by norm_num) (by norm_num) hdiv
