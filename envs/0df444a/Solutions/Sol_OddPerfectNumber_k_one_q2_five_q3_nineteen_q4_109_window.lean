-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_q4_109_window
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T20:45:37.772652+00:00
-- url     : https://prove2.me/submissions/65c36f6a-3f44-44fa-a804-d436cc8b2fe7

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_eight
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_six_sharp
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_nineteen_ge_four
import Theorems.Thm_OddPerfectNumber_geom_sum_last_three_terms_le
import Theorems.Thm_OddPerfectNumber_geom_sum_cross_lt_of_le

theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 19 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2) (hDlow : 225 ≤ D)
    (hp_eq : p = 2 * D - 1) (hq4 : q4 = 109)
    (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) :
    379 ≤ D ∧ D ≤ 398 := by
  subst q4
  let S3 := ∑ i ∈ Finset.range (2*a + 1), 3 ^ i
  let S5 := ∑ i ∈ Finset.range (2*b + 1), 5 ^ i
  let S19 := ∑ i ∈ Finset.range (2*c + 1), 19 ^ i
  let Sq := ∑ i ∈ Finset.range (2*e + 1), 109 ^ i
  have h3 := OddPerfectNumber.geom_ratio_lower_three_ge_eight (2*a) (by omega)
  have h5 := OddPerfectNumber.geom_ratio_lower_five_ge_six_sharp (2*b) (by omega)
  have h19 := OddPerfectNumber.geom_ratio_lower_nineteen_ge_four (2*c) (by omega)
  have hlast := OddPerfectNumber.geom_sum_last_three_terms_le 109 (2*e) (by omega)
  have hE1 : 2*e = (2*e - 2) + 2 := by omega
  have hE2 : 2*e - 1 = (2*e - 2) + 1 := by omega
  have hq : 11991 * 109^(2*e) ≤ 11881 * Sq := by
    have hpow1 : 109^(2*e) = 109^2 * 109^(2*e-2) := by
      calc
        109^(2*e) = 109^((2*e-2)+2) := by congr 1 <;> omega
        _ = 109^2 * 109^(2*e-2) := by rw [pow_add]; ring
    have hpow2 : 109^(2*e-1) = 109 * 109^(2*e-2) := by
      calc
        109^(2*e-1) = 109^((2*e-2)+1) := by congr 1 <;> omega
        _ = 109 * 109^(2*e-2) := by rw [pow_add]; ring
    have hpow3 : 109^(2*e-2) = 109^(2*e-2) := rfl
    calc
      11991 * 109^(2*e) = 11881 * (109^(2*e) + 109^(2*e-1) + 109^(2*e-2)) := by rw [hpow1, hpow2]; ring
      _ ≤ 11881 * Sq := Nat.mul_le_mul_left 11881 (by simpa [Sq] using hlast)
  have hmul35 := Nat.mul_le_mul h3 h5
  have hmul19q := Nat.mul_le_mul h19 hq
  have hmul := Nat.mul_le_mul hmul35 hmul19q
  have hcross :
      317040277219050021 * (3^(2*a) * 5^(2*b) * 19^(2*c) * 109^(2*e)) ≤
        158729432474390625 * (S3 * S5 * S19 * Sq) := by
    calc
      317040277219050021 * (3^(2*a) * 5^(2*b) * 19^(2*c) * 109^(2*e)) =
          (9841*3^(2*a)) * (19531*5^(2*b)) * ((137561*19^(2*c)) * (11991*109^(2*e))) := by ring
      _ ≤ (6561*S3) * (15625*S5) * ((130321*S19) * (11881*Sq)) := by simpa only [S3, S5, S19, Sq] using hmul
      _ = 158729432474390625 * (S3*S5*S19*Sq) := by ring
  have hmpos : 0 < m^2 := by rw [hfac]; positivity
  have hineq : 317040277219050021 * D * (m^2) ≤ 158729432474390625 * p * (m^2) := by
    have hmulD := Nat.mul_le_mul_left D hcross
    calc
      317040277219050021 * D * (m^2) = D * (317040277219050021 * (3^(2*a)*5^(2*b)*19^(2*c)*109^(2*e))) := by rw [hfac]; ring
      _ ≤ D * (158729432474390625 * (S3*S5*S19*Sq)) := hmulD
      _ = 158729432474390625 * (D*sigma) := by rw [hsigma]; ring
      _ = 158729432474390625 * (p*(m^2)) := by rw [hrel]
      _ = 158729432474390625 * p * (m^2) := by ring
  have hcoef : 317040277219050021 * D ≤ 158729432474390625 * p := by
    apply Nat.le_of_mul_le_mul_right (by simpa [Nat.mul_assoc] using hineq)
    exact hmpos
  have hD379 : 379 ≤ D := by
    by_contra hbad
    have hle : D ≤ 853 := by omega
    rw [hp_eq] at hcoef
    omega
  have hu3 := OddPerfectNumber.geom_sum_cross_lt_of_le 3 3 (2*a) (by norm_num) (by norm_num) (by norm_num)
  have hu5 := OddPerfectNumber.geom_sum_cross_lt_of_le 5 5 (2*b) (by norm_num) (by norm_num) (by norm_num)
  have hu19 := OddPerfectNumber.geom_sum_cross_lt_of_le 19 19 (2*c) (by norm_num) (by norm_num) (by norm_num)
  have huq := OddPerfectNumber.geom_sum_cross_lt_of_le 109 109 (2*e) (by norm_num) (by norm_num) (by norm_num)
  have hu35 := Nat.mul_lt_mul_of_lt_of_lt hu3 hu5
  have hu19q := Nat.mul_lt_mul_of_lt_of_lt hu19 huq
  have hu := Nat.mul_lt_mul_of_lt_of_lt hu35 hu19q
  norm_num at hu
  have hupper : 15552 * sigma < 31065 * (m^2) := by
    calc
      15552*sigma = (2*S3)*(4*S5)*(18*S19)*(108 * Sq) := by rw [hsigma]; dsimp [S3,S5,S19,Sq]; ring
      _ < (3*3^(2*a))*(5*5^(2*b))*((19*19^(2*c))*(109*109^(2*e))) := by simpa [S3,S5,S19,Sq, Nat.mul_assoc] using hu
      _ = 31065*(m^2) := by rw [hfac]; ring
  have hineqU : 15552*p*(m^2) < 31065*D*(m^2) := by
    calc
      15552*p*(m^2) = 15552*(p*(m^2)) := by ring
      _ = 15552*(D*sigma) := by rw [hrel]
      _ = D*(15552*sigma) := by ring
      _ < D*(31065*(m^2)) := (Nat.mul_lt_mul_left (by omega)).2 hupper
      _ = 31065*D*(m^2) := by ring
  have hcoefU : 15552*p < 31065*D := by
    apply Nat.lt_of_mul_lt_mul_right (by simpa [Nat.mul_assoc] using hineqU)
  have hD398 : D ≤ 398 := by
    by_contra hbad
    have hge : 961 ≤ D := by omega
    rw [hp_eq] at hcoefU
    omega
  exact ⟨hD379, hD398⟩






