-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_b_one_D27_q4_31_absurd_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T05:28:57.57975+00:00
-- url     : https://prove2.me/submissions/7d007473-baae-4015-80fc-f3ba379859e9

import Mathlib
import Theorems.Thm_OddPerfectNumber_q2_five_q3_twentynine_D27_source_bridge_v1
import Theorems.Thm_OddPerfectNumber_geom_sum_not_dvd_of_order_certificate
import Theorems.Thm_OddPerfectNumber_even_order_31_mod_53_v2

open OddPerfectNumber

theorem solution (D p sigma m a b c e q4 : Nat)
    (hrel : D * sigma = p * m ^ 2) (hD : D = 27) (hp_eq : p = 2 * D - 1)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hq4eq : q4 = 31) (he : 0 < e) :
    False := by
  subst hq4eq
  have hsrc : 53 ∣ ∑ i ∈ Finset.range (2 * e + 1), 31 ^ i :=
    q2_five_q3_twentynine_D27_source_bridge_v1 D p sigma m a b c e 31
      hrel hD hp_eq hsigma
  have hnot : ¬ orderOf (31 : ZMod 53) ∣ 2 * e + 1 := by
    intro hdvd
    have h2 : 2 ∣ orderOf (31 : ZMod 53) :=
      even_iff_two_dvd.mp even_order_31_mod_53_v2
    have h2odd : 2 ∣ 2 * e + 1 := dvd_trans h2 hdvd
    omega
  exact (geom_sum_not_dvd_of_order_certificate hnot) hsrc
