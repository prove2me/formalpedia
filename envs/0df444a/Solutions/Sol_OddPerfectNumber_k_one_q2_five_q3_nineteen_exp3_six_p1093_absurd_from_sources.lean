-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_exp3_six_p1093_absurd_from_sources
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T03:27:24.555514+00:00
-- url     : https://prove2.me/submissions/122d16b5-1043-4bc7-9d5a-a210407627be

import Mathlib
import Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_exp3_six_p1093_five_dvd_sigma
import Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_547_product_no_five

theorem solution (m d sigma a b c e : Nat)
    (hprod : m ^ 2 = 547 * d)
    (hsigma_eq : sigma = 1093 * d)
    (hpow : 5 ^ 6 ∣ m ^ 2)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (e + 1), 547 ^ i))
    (h3 : ¬ 5 ∣ ∑ i ∈ Finset.range (a + 1), 3 ^ i)
    (h19 : ¬ 5 ∣ ∑ i ∈ Finset.range (c + 1), 19 ^ i)
    (h547 : ¬ 5 ∣ ∑ i ∈ Finset.range (e + 1), 547 ^ i) :
    False := by
  have h5sigma : 5 ∣ sigma :=
    OddPerfectNumber.q2_five_q3_nineteen_exp3_six_p1093_five_dvd_sigma
      m d sigma hprod hsigma_eq hpow
  have hno5 : ¬ 5 ∣
      (∑ i ∈ Finset.range (a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (e + 1), 547 ^ i) :=
    OddPerfectNumber.q2_five_q3_nineteen_q4_547_product_no_five
      a b c e h3 h19 h547
  exact hno5 (by simpa [hsigma] using h5sigma)
