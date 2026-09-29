-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_q4_593_no_local_sigma_source
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T20:18:52.146754+00:00
-- url     : https://prove2.me/submissions/91b6319a-f594-4134-aeae-a4a755043545

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_not_dvd_of_order_certificate
import Theorems.Thm_OddPerfectNumber_prime_not_dvd_own_sigma_prime_pow

theorem solution (sigma a b c e : Nat)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2 * a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2 * b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2 * c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (2 * e + 1), 593 ^ i))
    (hdiv : 593 ∣ sigma)
    (h3 : ¬ orderOf (3 : ZMod 593) ∣ 2 * a + 1)
    (h5 : ¬ orderOf (5 : ZMod 593) ∣ 2 * b + 1)
    (h19 : ¬ orderOf (19 : ZMod 593) ∣ 2 * c + 1) :
    False := by
  have hno3 := OddPerfectNumber.geom_sum_not_dvd_of_order_certificate
    (p := 593) (q := 3) (e := a) h3
  have hno5 := OddPerfectNumber.geom_sum_not_dvd_of_order_certificate
    (p := 593) (q := 5) (e := b) h5
  have hno19 := OddPerfectNumber.geom_sum_not_dvd_of_order_certificate
    (p := 593) (q := 19) (e := c) h19
  have hno593 : ¬ 593 ∣ ∑ i ∈ Finset.range (2 * e + 1), 593 ^ i :=
    OddPerfectNumber.prime_not_dvd_own_sigma_prime_pow 593 (2 * e) (by norm_num)
  have hp : Nat.Prime 593 := by norm_num
  have h := hdiv
  rw [hsigma] at h
  rcases hp.dvd_mul.mp h with hleft | h593div
  · rcases hp.dvd_mul.mp hleft with hleft' | h19div
    · rcases hp.dvd_mul.mp hleft' with h3div | h5div
      · exact hno3 h3div
      · exact hno5 h5div
    · exact hno19 h19div
  · exact hno593 h593div
