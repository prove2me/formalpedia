-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_D45_q4_31_canonical_floors_absurd_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T05:42:50.921207+00:00
-- url     : https://prove2.me/submissions/f83fb9d1-54da-4a92-97c3-b55160976699

-- v2: mul_le_mul association fix (native chain shape, ring rearranges)
import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_eight
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_six
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_thirtyone_ge_two
import Theorems.Thm_OddPerfectNumber_geom_sum_last_two_terms_le

open OddPerfectNumber

theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hD : D = 45) (hp_eq : p = 2 * D - 1) (hq4 : q4 = 31)
    (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) :
    False := by
  subst hq4
  have h8 : 8 ≤ 2 * a := by omega
  have h6 : 6 ≤ 2 * b := by omega
  have h2 : 2 ≤ 2 * e := by omega
  have hC1 : 1 ≤ 2 * c := by omega
  have h3 := geom_ratio_lower_three_ge_eight (2 * a) h8
  have h5 := geom_ratio_lower_five_ge_six (2 * b) h6
  have h31 := geom_ratio_lower_thirtyone_ge_two (2 * e) h2
  have h29 := geom_sum_last_two_terms_le 29 (2 * c) hC1
  have h29C : 29 ^ (2 * c) = 29 * 29 ^ (2 * c - 1) := by
    conv_lhs => rw [← Nat.add_sub_cancel' hC1]
    rw [pow_add, pow_one]
  have h29' : 30 * 29 ^ (2 * c - 1) ≤ ∑ i ∈ Finset.range (2 * c + 1), 29 ^ i := by
    have h30 : 29 ^ (2 * c) + 29 ^ (2 * c - 1) = 30 * 29 ^ (2 * c - 1) := by
      rw [h29C]; ring
    omega
  have e1 := Nat.mul_le_mul h3 h5
  have e2 := Nat.mul_le_mul e1 h31
  have e3 := Nat.mul_le_mul e2 h29'
  have e3b : 45 * (9841 * 3 ^ (2*a) * (3906 * 5 ^ (2*b)) * (993 * 31 ^ (2*e)) * (30 * 29 ^ (2*c - 1)))
      ≤ 45 * ((6561 * ∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (3125 * ∑ i ∈ Finset.range (2*b + 1), 5 ^ i) * (961 * ∑ i ∈ Finset.range (2*e + 1), 31 ^ i) * ∑ i ∈ Finset.range (2*c + 1), 29 ^ i) :=
    Nat.mul_le_mul (le_refl 45) e3
  have r1 : 45 * (9841 * 3 ^ (2*a) * (3906 * 5 ^ (2*b)) * (993 * 31 ^ (2*e)) * (30 * 29 ^ (2*c - 1)))
      = 51529329060300 * (3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c - 1) * 31 ^ (2*e)) := by
    ring
  have r2 : 45 * ((6561 * ∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (3125 * ∑ i ∈ Finset.range (2*b + 1), 5 ^ i) * (961 * ∑ i ∈ Finset.range (2*e + 1), 31 ^ i) * ∑ i ∈ Finset.range (2*c + 1), 29 ^ i)
      = 886657640625 * sigma := by
    rw [hsigma]; ring
  have hLow : 51529329060300 * (3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c - 1) * 31 ^ (2*e))
      ≤ 886657640625 * sigma := by
    rw [← r1, ← r2]; exact e3b
  have hp89 : p = 89 := by omega
  have hrel45 : 45 * sigma = 89 * m ^ 2 := by
    rw [← hD, ← hp89]; exact hrel
  have hm2 : m ^ 2 = 29 * (3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c - 1) * 31 ^ (2*e)) := by
    rw [hfac, h29C]; ring
  have hU : 886657640625 * sigma
      = 50854741565625 * (3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c - 1) * 31 ^ (2*e)) := by
    have hM : 886657640625 * sigma = 19703503125 * (45 * sigma) := by ring
    rw [hM, hrel45, hm2]; ring
  have hXpos : 0 < 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c - 1) * 31 ^ (2*e) := by
    positivity
  have hle : 51529329060300 * (3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c - 1) * 31 ^ (2*e))
      ≤ 50854741565625 * (3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c - 1) * 31 ^ (2*e)) := by
    rw [← hU]; exact hLow
  have hLU : 51529329060300 ≤ 50854741565625 :=
    le_of_mul_le_mul_right hle hXpos
  norm_num at hLU
