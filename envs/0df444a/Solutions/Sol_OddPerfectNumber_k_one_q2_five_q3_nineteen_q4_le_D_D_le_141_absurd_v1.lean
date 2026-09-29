-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_q4_le_D_D_le_141_absurd_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-16T17:51:06.536051+00:00
-- url     : https://prove2.me/submissions/c24b33d6-a546-40d5-a67a-7c3bc06003f8

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_q4_le_141_ratio_v1
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_eight
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_six_sharp
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_nineteen_ge_four

theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 19 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2) (hDlow : 1 ≤ D) (hDodd : Odd D)
    (hDle : D ≤ 141) (hp : p.Prime) (hp_eq : p = 2 * D - 1)
    (hq4prime : q4.Prime) (hq4gt : 19 < q4) (hq4leD : q4 ≤ D)
    (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) : False := by
  let S3 := ∑ i ∈ Finset.range (2*a + 1), 3 ^ i
  let S5 := ∑ i ∈ Finset.range (2*b + 1), 5 ^ i
  let S19 := ∑ i ∈ Finset.range (2*c + 1), 19 ^ i
  let Sq := ∑ i ∈ Finset.range (2*e + 1), q4 ^ i
  have h3 := OddPerfectNumber.geom_ratio_lower_three_ge_eight (2*a) (by omega)
  have h5 := OddPerfectNumber.geom_ratio_lower_five_ge_six_sharp (2*b) (by omega)
  have h19 := OddPerfectNumber.geom_ratio_lower_nineteen_ge_four (2*c) (by omega)
  have hq4le : q4 ≤ 141 := by omega
  have hq := OddPerfectNumber.k_one_q2_five_q3_nineteen_q4_le_141_ratio_v1 q4 e hq4gt hq4le he
  have hmul35 := Nat.mul_le_mul h3 h5
  have hmul19q := Nat.mul_le_mul h19 hq
  have hmul := Nat.mul_le_mul hmul35 hmul19q
  have hcross :
      (9841*19531*137561*20023) *
          (3^(2*a) * 5^(2*b) * 19^(2*c) * q4^(2*e)) ≤
        (6561*15625*130321*19881) * (S3*S5*S19*Sq) := by
    calc
      (9841*19531*137561*20023) *
          (3^(2*a) * 5^(2*b) * 19^(2*c) * q4^(2*e)) =
          (9841*3^(2*a)) * (19531*5^(2*b)) *
            ((137561*19^(2*c)) * (20023*q4^(2*e))) := by ring
      _ ≤ (6561*S3) * (15625*S5) *
            ((130321*S19) * (19881*Sq)) := by
              simpa only [S3, S5, S19, Sq] using hmul
      _ = (6561*15625*130321*19881) * (S3*S5*S19*Sq) := by ring
  have hmpos : 0 < m^2 := by rw [hfac]; positivity
  have hineq :
      (9841*19531*137561*20023) * D * (m^2) ≤
        (6561*15625*130321*19881) * p * (m^2) := by
    have hmulD := Nat.mul_le_mul_left D hcross
    calc
      (9841*19531*137561*20023) * D * (m^2) =
          D * ((9841*19531*137561*20023) *
            (3^(2*a) * 5^(2*b) * 19^(2*c) * q4^(2*e))) := by
              rw [hfac]
              ring
      _ ≤ D * ((6561*15625*130321*19881) * (S3*S5*S19*Sq)) := hmulD
      _ = (6561*15625*130321*19881) * (D*sigma) := by rw [hsigma]; ring
      _ = (6561*15625*130321*19881) * (p*(m^2)) := by rw [hrel]
      _ = (6561*15625*130321*19881) * p * (m^2) := by ring
  have hcoef :
      (9841*19531*137561*20023) * D ≤
        (6561*15625*130321*19881) * p := by
    apply Nat.le_of_mul_le_mul_right (by simpa [Nat.mul_assoc] using hineq)
    exact hmpos
  rw [hp_eq] at hcoef
  norm_num at hcoef
  omega
