-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_q4_103_window
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T20:44:38.71824+00:00
-- url     : https://prove2.me/submissions/cc989cab-9803-42f0-9592-9742d295807c

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
    (hp_eq : p = 2 * D - 1) (hq4 : q4 = 103)
    (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) :
    642 ≤ D ∧ D ≤ 699 := by
  subst q4
  let S3 := ∑ i ∈ Finset.range (2*a + 1), 3 ^ i
  let S5 := ∑ i ∈ Finset.range (2*b + 1), 5 ^ i
  let S19 := ∑ i ∈ Finset.range (2*c + 1), 19 ^ i
  let Sq := ∑ i ∈ Finset.range (2*e + 1), 103 ^ i
  have h3 := OddPerfectNumber.geom_ratio_lower_three_ge_eight (2*a) (by omega)
  have h5 := OddPerfectNumber.geom_ratio_lower_five_ge_six_sharp (2*b) (by omega)
  have h19 := OddPerfectNumber.geom_ratio_lower_nineteen_ge_four (2*c) (by omega)
  have hlast := OddPerfectNumber.geom_sum_last_three_terms_le 103 (2*e) (by omega)
  have hE1 : 2*e = (2*e - 2) + 2 := by omega
  have hE2 : 2*e - 1 = (2*e - 2) + 1 := by omega
  have hq : 10713 * 103^(2*e) ≤ 10609 * Sq := by
    have hpow1 : 103^(2*e) = 103^2 * 103^(2*e-2) := by
      calc
        103^(2*e) = 103^((2*e-2)+2) := by congr 1 <;> omega
        _ = 103^2 * 103^(2*e-2) := by rw [pow_add]; ring
    have hpow2 : 103^(2*e-1) = 103 * 103^(2*e-2) := by
      calc
        103^(2*e-1) = 103^((2*e-2)+1) := by congr 1 <;> omega
        _ = 103 * 103^(2*e-2) := by rw [pow_add]; ring
    have hpow3 : 103^(2*e-2) = 103^(2*e-2) := rfl
    calc
      10713 * 103^(2*e) = 10609 * (103^(2*e) + 103^(2*e-1) + 103^(2*e-2)) := by rw [hpow1, hpow2]; ring
      _ ≤ 10609 * Sq := Nat.mul_le_mul_left 10609 (by simpa [Sq] using hlast)
  have hmul35 := Nat.mul_le_mul h3 h5
  have hmul19q := Nat.mul_le_mul h19 hq
  have hmul := Nat.mul_le_mul hmul35 hmul19q
  have hcross :
      283250145096129003 * (3^(2*a) * 5^(2*b) * 19^(2*c) * 103^(2*e)) ≤
        141735590364515625 * (S3 * S5 * S19 * Sq) := by
    calc
      283250145096129003 * (3^(2*a) * 5^(2*b) * 19^(2*c) * 103^(2*e)) =
          (9841*3^(2*a)) * (19531*5^(2*b)) * ((137561*19^(2*c)) * (10713*103^(2*e))) := by ring
      _ ≤ (6561*S3) * (15625*S5) * ((130321*S19) * (10609*Sq)) := by simpa only [S3, S5, S19, Sq] using hmul
      _ = 141735590364515625 * (S3*S5*S19*Sq) := by ring
  have hmpos : 0 < m^2 := by rw [hfac]; positivity
  have hineq : 283250145096129003 * D * (m^2) ≤ 141735590364515625 * p * (m^2) := by
    have hmulD := Nat.mul_le_mul_left D hcross
    calc
      283250145096129003 * D * (m^2) = D * (283250145096129003 * (3^(2*a)*5^(2*b)*19^(2*c)*103^(2*e))) := by rw [hfac]; ring
      _ ≤ D * (141735590364515625 * (S3*S5*S19*Sq)) := hmulD
      _ = 141735590364515625 * (D*sigma) := by rw [hsigma]; ring
      _ = 141735590364515625 * (p*(m^2)) := by rw [hrel]
      _ = 141735590364515625 * p * (m^2) := by ring
  have hcoef : 283250145096129003 * D ≤ 141735590364515625 * p := by
    apply Nat.le_of_mul_le_mul_right (by simpa [Nat.mul_assoc] using hineq)
    exact hmpos
  have hD642 : 642 ≤ D := by
    by_contra hbad
    have hle : D ≤ 853 := by omega
    rw [hp_eq] at hcoef
    omega
  have hu3 := OddPerfectNumber.geom_sum_cross_lt_of_le 3 3 (2*a) (by norm_num) (by norm_num) (by norm_num)
  have hu5 := OddPerfectNumber.geom_sum_cross_lt_of_le 5 5 (2*b) (by norm_num) (by norm_num) (by norm_num)
  have hu19 := OddPerfectNumber.geom_sum_cross_lt_of_le 19 19 (2*c) (by norm_num) (by norm_num) (by norm_num)
  have huq := OddPerfectNumber.geom_sum_cross_lt_of_le 103 103 (2*e) (by norm_num) (by norm_num) (by norm_num)
  have hu35 := Nat.mul_lt_mul_of_lt_of_lt hu3 hu5
  have hu19q := Nat.mul_lt_mul_of_lt_of_lt hu19 huq
  have hu := Nat.mul_lt_mul_of_lt_of_lt hu35 hu19q
  norm_num at hu
  have hupper : 14688 * sigma < 29355 * (m^2) := by
    calc
      14688*sigma = (2*S3)*(4*S5)*(18*S19)*(102 * Sq) := by rw [hsigma]; dsimp [S3,S5,S19,Sq]; ring
      _ < (3*3^(2*a))*(5*5^(2*b))*((19*19^(2*c))*(103*103^(2*e))) := by simpa [S3,S5,S19,Sq, Nat.mul_assoc] using hu
      _ = 29355*(m^2) := by rw [hfac]; ring
  have hineqU : 14688*p*(m^2) < 29355*D*(m^2) := by
    calc
      14688*p*(m^2) = 14688*(p*(m^2)) := by ring
      _ = 14688*(D*sigma) := by rw [hrel]
      _ = D*(14688*sigma) := by ring
      _ < D*(29355*(m^2)) := (Nat.mul_lt_mul_left (by omega)).2 hupper
      _ = 29355*D*(m^2) := by ring
  have hcoefU : 14688*p < 29355*D := by
    apply Nat.lt_of_mul_lt_mul_right (by simpa [Nat.mul_assoc] using hineqU)
  have hD699 : D ≤ 699 := by
    by_contra hbad
    have hge : 961 ≤ D := by omega
    rw [hp_eq] at hcoefU
    omega
  exact ⟨hD642, hD699⟩






