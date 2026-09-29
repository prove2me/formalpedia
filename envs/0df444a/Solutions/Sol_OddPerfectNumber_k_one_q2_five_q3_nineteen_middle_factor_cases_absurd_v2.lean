-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_middle_factor_cases_absurd_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-17T07:30:06.548088+00:00
-- url     : https://prove2.me/submissions/58834f22-7de7-4337-8634-d216eddba624

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_eight
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_six_sharp
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_nineteen_ge_four
import Theorems.Thm_OddPerfectNumber_geom_sum_last_three_terms_le
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_terms_exact_v2

theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 19 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), (3 : Nat) ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), (5 : Nat) ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), (19 : Nat) ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hcases : (D = 159 ∧ q4 = 53 ∧ p = 317) ∨
      (D = 177 ∧ q4 = 59 ∧ p = 353) ∨
      (D = 201 ∧ q4 = 67 ∧ p = 401) ∨
      (D = 205 ∧ q4 = 41 ∧ p = 409))
    (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) : False := by
  let S3 : Nat := ∑ i ∈ Finset.range (2*a + 1), (3 : Nat) ^ i
  let S5 : Nat := ∑ i ∈ Finset.range (2*b + 1), (5 : Nat) ^ i
  let S19 : Nat := ∑ i ∈ Finset.range (2*c + 1), (19 : Nat) ^ i
  let Sq : Nat := ∑ i ∈ Finset.range (2*e + 1), q4 ^ i
  have hq4pos : 0 < q4 := by
    rcases hcases with h | h | h | h <;> omega
  have h3 := OddPerfectNumber.geom_ratio_lower_three_ge_eight (2*a) (by omega)
  have h5 := OddPerfectNumber.geom_ratio_lower_five_ge_six_sharp (2*b) (by omega)
  have h19 := OddPerfectNumber.geom_ratio_lower_nineteen_ge_four (2*c) (by omega)
  have hq := OddPerfectNumber.geom_ratio_lower_three_terms_exact_v2 q4 e he
  have hmul35 := Nat.mul_le_mul h3 h5
  have hmul19q := Nat.mul_le_mul h19 hq
  have hmul := Nat.mul_le_mul hmul35 hmul19q
  have hcross :
      (9841*19531*137561*(q4^2 + q4 + 1)) *
          (3^(2*a) * 5^(2*b) * 19^(2*c) * q4^(2*e)) ≤
        (6561*15625*130321*(q4^2)) * (S3*S5*S19*Sq) := by
    calc
      (9841*19531*137561*(q4^2 + q4 + 1)) *
          (3^(2*a) * 5^(2*b) * 19^(2*c) * q4^(2*e)) =
          (9841*3^(2*a)) * (19531*5^(2*b)) *
            ((137561*19^(2*c)) * ((q4^2 + q4 + 1)*q4^(2*e))) := by ring
      _ ≤ (6561*S3) * (15625*S5) *
            ((130321*S19) * ((q4^2)*Sq)) := by
              simpa only [S3, S5, S19, Sq] using hmul
      _ = (6561*15625*130321*(q4^2)) * (S3*S5*S19*Sq) := by ring
  have hmpos : 0 < m^2 := by
    rw [hfac]
    have h3p : 0 < (3:Nat)^(2*a) := by positivity
    have h5p : 0 < (5:Nat)^(2*b) := by positivity
    have h19p : 0 < (19:Nat)^(2*c) := by positivity
    have hqp : 0 < q4^(2*e) := by positivity
    positivity
  have hineq :
      (9841*19531*137561*(q4^2 + q4 + 1)) * D * (m^2) ≤
        (6561*15625*130321*(q4^2)) * p * (m^2) := by
    have hmulD := Nat.mul_le_mul_left D hcross
    calc
      (9841*19531*137561*(q4^2 + q4 + 1)) * D * (m^2) =
          D * ((9841*19531*137561*(q4^2 + q4 + 1)) *
            (3^(2*a) * 5^(2*b) * 19^(2*c) * q4^(2*e))) := by
              rw [hfac]
              ring
      _ ≤ D * ((6561*15625*130321*(q4^2)) * (S3*S5*S19*Sq)) := hmulD
      _ = (6561*15625*130321*(q4^2)) * (D*sigma) := by rw [hsigma]; ring
      _ = (6561*15625*130321*(q4^2)) * (p*(m^2)) := by rw [hrel]
      _ = (6561*15625*130321*(q4^2)) * p * (m^2) := by ring
  have hcoef :
      (9841*19531*137561*(q4^2 + q4 + 1)) * D ≤
        (6561*15625*130321*(q4^2)) * p := by
    exact le_of_mul_le_mul_right hineq hmpos
  rcases hcases with h | h | h | h
  all_goals rcases h with ⟨hD, hq4, hp⟩
  all_goals subst D
  all_goals subst q4
  all_goals subst p
  all_goals norm_num at hcoef
