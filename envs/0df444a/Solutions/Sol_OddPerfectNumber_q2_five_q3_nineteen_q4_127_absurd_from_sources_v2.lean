-- Prove2me | solution 1 for OddPerfectNumber.q2_five_q3_nineteen_q4_127_absurd_from_sources_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T07:54:50.3211+00:00
-- url     : https://prove2.me/submissions/dbfd3658-2963-4917-9865-8148c5b4fde3

import Mathlib
import Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_127_product_no_five
import Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_127_five_dvd_sigma_v2

theorem solution (p m d sigma a b c e : Nat)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsigma_eq : sigma = p * d)
    (hD : (p + 1) / 2 < 185)
    (hpow : 5 ^ 6 ∣ m ^ 2)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (e + 1), 127 ^ i))
    (h3 : ¬ 5 ∣ ∑ i ∈ Finset.range (a + 1), 3 ^ i)
    (h19 : ¬ 5 ∣ ∑ i ∈ Finset.range (c + 1), 19 ^ i)
    (h127 : ¬ 5 ∣ ∑ i ∈ Finset.range (e + 1), 127 ^ i) :
    False := by
  have hsigma_pos : 0 < sigma := by
    rw [hsigma]
    positivity
  have hpd_pos : 0 < p * d := by
    rw [← hsigma_eq]
    exact hsigma_pos
  have hp_ne : p ≠ 0 := by
    intro hp0
    subst p
    simp at hpd_pos
  have hp_pos : 0 < p := Nat.pos_of_ne_zero hp_ne
  have hDpos : 0 < (p + 1) / 2 := by
    omega
  have hfive : 5 ∣ sigma :=
    OddPerfectNumber.q2_five_q3_nineteen_q4_127_five_dvd_sigma_v2
      p m d sigma hprod hsigma_eq hDpos hD hpow
  have hfive_prod :
      5 ∣
        (∑ i ∈ Finset.range (a + 1), 3 ^ i) *
        (∑ i ∈ Finset.range (b + 1), 5 ^ i) *
        (∑ i ∈ Finset.range (c + 1), 19 ^ i) *
        (∑ i ∈ Finset.range (e + 1), 127 ^ i) := by
    rw [← hsigma]
    exact hfive
  exact OddPerfectNumber.q2_five_q3_nineteen_q4_127_product_no_five
    a b c e h3 h19 h127 hfive_prod
