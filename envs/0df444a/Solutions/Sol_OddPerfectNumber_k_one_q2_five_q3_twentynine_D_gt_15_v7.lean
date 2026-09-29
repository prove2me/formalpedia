-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_D_gt_15_v7
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T08:43:44.445584+00:00
-- url     : https://prove2.me/submissions/7c2bb337-6158-4e81-8c84-12d1d1d510c6

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_eight
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_six_sharp
import Theorems.Thm_OddPerfectNumber_geom_sum_last_two_terms_le
import Theorems.Thm_OddPerfectNumber_geom_sum_last_three_terms_le

theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2) (hp : p.Prime)
    (hp_eq : p = 2 * D - 1) (hq4gt : 29 < q4)
    (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) :
    15 < D := by
  let S3 := ∑ i ∈ Finset.range (2*a + 1), 3 ^ i
  let S5 := ∑ i ∈ Finset.range (2*b + 1), 5 ^ i
  let S29 := ∑ i ∈ Finset.range (2*c + 1), 29 ^ i
  let Sq := ∑ i ∈ Finset.range (2*e + 1), q4 ^ i
  have h3 := OddPerfectNumber.geom_ratio_lower_three_ge_eight (2*a) (by omega)
  have h5 := OddPerfectNumber.geom_ratio_lower_five_ge_six_sharp (2*b) (by omega)
  have hlast29 := OddPerfectNumber.geom_sum_last_two_terms_le 29 (2*c) (by omega)
  have hpow29 : 29 ^ (2*c) = 29 ^ (2*c - 1) * 29 := by
    calc
      29 ^ (2*c) = 29 ^ ((2*c - 1) + 1) := by congr 1 <;> omega
      _ = 29 ^ (2*c - 1) * 29 := by rw [pow_succ]
  have h29 : 30 * 29 ^ (2*c) ≤ 29 * S29 := by
    dsimp [S29] at hlast29 ⊢
    nlinarith [hlast29, hpow29]
  have hlastq := OddPerfectNumber.geom_sum_last_three_terms_le q4 (2*e) (by omega)
  have hpowq1 : q4 ^ (2*e) = q4 ^ 2 * q4 ^ (2*e - 2) := by
    calc
      q4 ^ (2*e) = q4 ^ ((2*e - 2) + 2) := by congr 1 <;> omega
      _ = q4 ^ 2 * q4 ^ (2*e - 2) := by rw [pow_add]; ring
  have hpowq2 : q4 ^ (2*e - 1) = q4 * q4 ^ (2*e - 2) := by
    calc
      q4 ^ (2*e - 1) = q4 ^ ((2*e - 2) + 1) := by congr 1 <;> omega
      _ = q4 * q4 ^ (2*e - 2) := by rw [pow_add]; ring
  have hqpoly : (q4^2 + q4 + 1) * q4^(2*e-2) ≤ Sq := by
    dsimp [Sq] at hlastq ⊢
    calc
      (q4^2 + q4 + 1) * q4^(2*e-2) =
          q4^2 * q4^(2*e-2) + q4 * q4^(2*e-2) + q4^(2*e-2) := by ring
      _ = q4^(2*e) + q4^(2*e-1) + q4^(2*e-2) := by
        rw [← hpowq1, ← hpowq2]
      _ ≤ ∑ i ∈ Finset.range (2*e + 1), q4^i := hlastq
  have hq : q4 ^ (2*e) ≤ Sq := by
    have hcoef : q4^2 * q4^(2*e-2) ≤
        (q4^2 + q4 + 1) * q4^(2*e-2) := by
      apply Nat.mul_le_mul_right
      omega
    calc
      q4 ^ (2*e) = q4^2 * q4^(2*e-2) := hpowq1
      _ ≤ (q4^2 + q4 + 1) * q4^(2*e-2) := hcoef
      _ ≤ Sq := hqpoly
  have hmul35 := Nat.mul_le_mul h3 h5
  have h29q := Nat.mul_le_mul h29 hq
  have hmul := Nat.mul_le_mul hmul35 h29q
  have hcross :
      5766137130 * (3^(2*a) * 5^(2*b) * 29^(2*c) * q4^(2*e)) ≤
        2972953125 * (S3 * S5 * S29 * Sq) := by
    calc
      5766137130 * (3^(2*a) * 5^(2*b) * 29^(2*c) * q4^(2*e)) =
          (9841*3^(2*a)) * (19531*5^(2*b)) *
            ((30*29^(2*c)) * (q4^(2*e))) := by ring
      _ ≤ (6561*S3) * (15625*S5) * ((29*S29) * Sq) := by
        simpa only [S3, S5, S29, Sq] using hmul
      _ = 2972953125 * (S3*S5*S29*Sq) := by ring
  have hmpos : 0 < m^2 := by rw [hfac]; positivity
  have hineq :
      5766137130 * D * (m^2) ≤ 2972953125 * p * (m^2) := by
    have hmulD := Nat.mul_le_mul_left D hcross
    calc
      5766137130 * D * (m^2) =
          D * (5766137130 *
            (3^(2*a)*5^(2*b)*29^(2*c)*q4^(2*e))) := by rw [hfac]; ring
      _ ≤ D * (2972953125 * (S3*S5*S29*Sq)) := hmulD
      _ = 2972953125 * (D*sigma) := by rw [hsigma]; ring
      _ = 2972953125 * (p*(m^2)) := by rw [hrel]
      _ = 2972953125 * p * (m^2) := by ring
  have hbound : 5766137130 * D ≤ 2972953125 * p := by
    apply Nat.le_of_mul_le_mul_right (by simpa [Nat.mul_assoc] using hineq)
    exact hmpos
  by_contra hD
  have hDle : D ≤ 15 := by omega
  rw [hp_eq] at hbound
  rw [hp_eq] at hp
  interval_cases D <;> norm_num at hp <;> norm_num <;> omega
