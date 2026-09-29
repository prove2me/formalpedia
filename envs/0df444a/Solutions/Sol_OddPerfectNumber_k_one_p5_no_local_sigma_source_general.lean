-- Prove2me | solution 1 for OddPerfectNumber.k_one_p5_no_local_sigma_source_general
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T04:49:25.695363+00:00
-- url     : https://prove2.me/submissions/b1404693-36d2-42fc-b9a3-2999edc552e1

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_not_dvd_of_order_certificate
import Theorems.Thm_OddPerfectNumber_prime_not_dvd_own_sigma_prime_pow

theorem solution (sigma a b c e q3 q4 : Nat)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2 * a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2 * b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2 * c + 1), q3 ^ i) *
      (∑ i ∈ Finset.range (2 * e + 1), q4 ^ i))
    (hdiv : 5 ∣ sigma)
    (h3 : ¬ orderOf (3 : ZMod 5) ∣ 2 * a + 1)
    (hq3 : ¬ orderOf (q3 : ZMod 5) ∣ 2 * c + 1)
    (hq4 : ¬ orderOf (q4 : ZMod 5) ∣ 2 * e + 1) :
    False := by
  have hno3 := OddPerfectNumber.geom_sum_not_dvd_of_order_certificate (p := 5) (q := 3) (e := a) h3
  have hnoq3 := OddPerfectNumber.geom_sum_not_dvd_of_order_certificate (p := 5) (q := q3) (e := c) hq3
  have hnoq4 := OddPerfectNumber.geom_sum_not_dvd_of_order_certificate (p := 5) (q := q4) (e := e) hq4
  have hno5 : ¬ 5 ∣ ∑ i ∈ Finset.range (2 * b + 1), 5 ^ i :=
    OddPerfectNumber.prime_not_dvd_own_sigma_prime_pow 5 (2 * b) (by norm_num)
  have hp : Nat.Prime 5 := by norm_num
  have h := hdiv
  rw [hsigma] at h
  rcases hp.dvd_mul.mp h with hleft | hq4div
  · rcases hp.dvd_mul.mp hleft with hleft' | hq3div
    · rcases hp.dvd_mul.mp hleft' with h3div | h5div
      · exact hno3 h3div
      · exact hno5 h5div
    · exact hnoq3 hq3div
  · exact hnoq4 hq4div
