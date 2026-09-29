-- Prove2me | solution 1 for OddPerfectNumber.k_one_p113_no_local_sigma_source_general
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T04:41:38.814521+00:00
-- url     : https://prove2.me/submissions/cab11de9-8d7a-43ff-8023-2049d3e979fb

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_not_dvd_of_order_certificate

theorem solution (sigma a b c e q4 : Nat)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2 * a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2 * b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2 * c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (2 * e + 1), q4 ^ i))
    (hdiv : 113 ∣ sigma)
    (h3 : ¬ orderOf (3 : ZMod 113) ∣ 2 * a + 1)
    (h5 : ¬ orderOf (5 : ZMod 113) ∣ 2 * b + 1)
    (h19 : ¬ orderOf (19 : ZMod 113) ∣ 2 * c + 1)
    (hq4 : ¬ orderOf (q4 : ZMod 113) ∣ 2 * e + 1) :
    False := by
  have hno3 := OddPerfectNumber.geom_sum_not_dvd_of_order_certificate (p := 113) (q := 3) (e := a) h3
  have hno5 := OddPerfectNumber.geom_sum_not_dvd_of_order_certificate (p := 113) (q := 5) (e := b) h5
  have hno19 := OddPerfectNumber.geom_sum_not_dvd_of_order_certificate (p := 113) (q := 19) (e := c) h19
  have hnoq4 := OddPerfectNumber.geom_sum_not_dvd_of_order_certificate (p := 113) (q := q4) (e := e) hq4
  have hp : Nat.Prime 113 := by norm_num
  have h := hdiv
  rw [hsigma] at h
  rcases hp.dvd_mul.mp h with hleft | hq4div
  · rcases hp.dvd_mul.mp hleft with hleft' | h19div
    · rcases hp.dvd_mul.mp hleft' with h3div | h5div
      · exact hno3 h3div
      · exact hno5 h5div
    · exact hno19 h19div
  · exact hnoq4 hq4div
