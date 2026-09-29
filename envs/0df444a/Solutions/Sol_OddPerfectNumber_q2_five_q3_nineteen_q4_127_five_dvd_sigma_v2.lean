-- Prove2me | solution 1 for OddPerfectNumber.q2_five_q3_nineteen_q4_127_five_dvd_sigma_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T07:05:54.173299+00:00
-- url     : https://prove2.me/submissions/c82139dc-74d9-4542-ab7a-2f1c93965469

import Mathlib
import Theorems.Thm_OddPerfectNumber_nat_prime_pow_dvd_of_dvd_mul_right

theorem solution (p m d sigma : Nat)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsigma : sigma = p * d)
    (hDpos : 0 < (p + 1) / 2)
    (hD : (p + 1) / 2 < 185)
    (hpow : 5 ^ 6 ∣ m ^ 2) :
    5 ∣ sigma := by
  have hpow' : 5 ^ 6 ∣ ((p + 1) / 2) * d := by
    simpa [hprod] using hpow
  have h5d : 5 ∣ d := by
    by_contra hnot
    have hDpow : 5 ^ 6 ∣ (p + 1) / 2 := by
      exact OddPerfectNumber.nat_prime_pow_dvd_of_dvd_mul_right
        5 ((p + 1) / 2) d 6 (by norm_num) hnot hpow'
    have hle : 5 ^ 6 ≤ (p + 1) / 2 :=
      Nat.le_of_dvd hDpos hDpow
    norm_num at hle
    omega
  rw [hsigma]
  exact dvd_mul_of_dvd_right h5d p
