-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_D45_q4_31_abundance_absurd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T22:59:55.119528+00:00
-- url     : https://prove2.me/submissions/cb6953f1-9e65-40bb-87d0-73f5d1005094

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_eight
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_six
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_thirtyone_ge_two
import Theorems.Thm_OddPerfectNumber_geom_sum_last_two_terms_le

theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hD : D = 45) (hp_eq : p = 2 * D - 1) (hq4 : q4 = 31)
    (ha : 8 ≤ a) (hb : 6 ≤ b) (hc : 4 ≤ c) (he : 2 ≤ e) :
    False := by
  subst q4
  let S3 := ∑ i ∈ Finset.range (2*a + 1), 3 ^ i
  let S5 := ∑ i ∈ Finset.range (2*b + 1), 5 ^ i
  let S29 := ∑ i ∈ Finset.range (2*c + 1), 29 ^ i
  let S31 := ∑ i ∈ Finset.range (2*e + 1), 31 ^ i
  have h3 := OddPerfectNumber.geom_ratio_lower_three_ge_eight (2*a) (by omega)
  have h5 := OddPerfectNumber.geom_ratio_lower_five_ge_six (2*b) (by omega)
  have h31 := OddPerfectNumber.geom_ratio_lower_thirtyone_ge_two (2*e) (by omega)
  have hlast := OddPerfectNumber.geom_sum_last_two_terms_le 29 (2*c) (by omega)
  have h29 : 30 * 29^(2*c) ≤ 29 * S29 := by
    have hpow : 29^(2*c) = 29^(2*c - 1) * 29 := by
      calc
        29^(2*c) = 29^((2*c - 1) + 1) := by congr 1 <;> omega
        _ = 29^(2*c - 1) * 29 := by rw [pow_succ]
    calc
      30 * 29^(2*c) = 29 * (29^(2*c) + 29^(2*c - 1)) := by rw [hpow]; ring
      _ ≤ 29 * S29 := Nat.mul_le_mul_left 29 (by simpa [S29] using hlast)
  have hmul35 := Nat.mul_le_mul h3 h5
  have hmul29q := Nat.mul_le_mul h29 h31
  have hmul := Nat.mul_le_mul hmul35 hmul29q
  have hcross :
      1145096201340 * (3^(2*a) * 5^(2*b) * 29^(2*c) * 31^(2*e)) ≤
        571401590625 * (S3 * S5 * S29 * S31) := by
    calc
      1145096201340 * (3^(2*a) * 5^(2*b) * 29^(2*c) * 31^(2*e)) =
          (9841*3^(2*a)) * (3906*5^(2*b)) *
            ((30*29^(2*c)) * (993*31^(2*e))) := by ring
      _ ≤ (6561*S3) * (3125*S5) * ((29*S29) * (961*S31)) := by
        simpa only [S3, S5, S29, S31] using hmul
      _ = 571401590625 * (S3*S5*S29*S31) := by ring
  have hmpos : 0 < m^2 := by rw [hfac]; positivity
  have hineq : 1145096201340 * D * (m^2) ≤ 571401590625 * p * (m^2) := by
    have hmulD := Nat.mul_le_mul_left D hcross
    calc
      1145096201340 * D * (m^2) =
          D * (1145096201340 * (3^(2*a) * 5^(2*b) * 29^(2*c) * 31^(2*e))) := by rw [hfac]; ring
      _ ≤ D * (571401590625 * (S3*S5*S29*S31)) := hmulD
      _ = 571401590625 * (D*sigma) := by rw [hsigma]; ring
      _ = 571401590625 * (p*(m^2)) := by rw [hrel]
      _ = 571401590625 * p * (m^2) := by ring
  have hconst : 571401590625 * p < 1145096201340 * D := by norm_num [hD, hp_eq]
  have hstrict : 571401590625 * p * (m^2) < 1145096201340 * D * (m^2) :=
    Nat.mul_lt_mul_of_pos_right hconst hmpos
  exact False.elim ((Nat.not_lt_of_ge hineq) hstrict)
