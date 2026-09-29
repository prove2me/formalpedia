-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_q4_107_window
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T20:45:06.558013+00:00
-- url     : https://prove2.me/submissions/e9e5be37-a517-43cd-ab6b-7625ba87288b

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
    (hp_eq : p = 2 * D - 1) (hq4 : q4 = 107)
    (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) :
    437 ≤ D ∧ D ≤ 462 := by
  subst q4
  let S3 := ∑ i ∈ Finset.range (2*a + 1), 3 ^ i
  let S5 := ∑ i ∈ Finset.range (2*b + 1), 5 ^ i
  let S19 := ∑ i ∈ Finset.range (2*c + 1), 19 ^ i
  let Sq := ∑ i ∈ Finset.range (2*e + 1), 107 ^ i
  have h3 := OddPerfectNumber.geom_ratio_lower_three_ge_eight (2*a) (by omega)
  have h5 := OddPerfectNumber.geom_ratio_lower_five_ge_six_sharp (2*b) (by omega)
  have h19 := OddPerfectNumber.geom_ratio_lower_nineteen_ge_four (2*c) (by omega)
  have hlast := OddPerfectNumber.geom_sum_last_three_terms_le 107 (2*e) (by omega)
  have hE1 : 2*e = (2*e - 2) + 2 := by omega
  have hE2 : 2*e - 1 = (2*e - 2) + 1 := by omega
  have hq : 11557 * 107^(2*e) ≤ 11449 * Sq := by
    have hpow1 : 107^(2*e) = 107^2 * 107^(2*e-2) := by
      calc
        107^(2*e) = 107^((2*e-2)+2) := by congr 1 <;> omega
        _ = 107^2 * 107^(2*e-2) := by rw [pow_add]; ring
    have hpow2 : 107^(2*e-1) = 107 * 107^(2*e-2) := by
      calc
        107^(2*e-1) = 107^((2*e-2)+1) := by congr 1 <;> omega
        _ = 107 * 107^(2*e-2) := by rw [pow_add]; ring
    have hpow3 : 107^(2*e-2) = 107^(2*e-2) := rfl
    calc
      11557 * 107^(2*e) = 11449 * (107^(2*e) + 107^(2*e-1) + 107^(2*e-2)) := by rw [hpow1, hpow2]; ring
      _ ≤ 11449 * Sq := Nat.mul_le_mul_left 11449 (by simpa [Sq] using hlast)
  have hmul35 := Nat.mul_le_mul h3 h5
  have hmul19q := Nat.mul_le_mul h19 hq
  have hmul := Nat.mul_le_mul hmul35 hmul19q
  have hcross :
      305565381020812367 * (3^(2*a) * 5^(2*b) * 19^(2*c) * 107^(2*e)) ≤
        152957938927640625 * (S3 * S5 * S19 * Sq) := by
    calc
      305565381020812367 * (3^(2*a) * 5^(2*b) * 19^(2*c) * 107^(2*e)) =
          (9841*3^(2*a)) * (19531*5^(2*b)) * ((137561*19^(2*c)) * (11557*107^(2*e))) := by ring
      _ ≤ (6561*S3) * (15625*S5) * ((130321*S19) * (11449*Sq)) := by simpa only [S3, S5, S19, Sq] using hmul
      _ = 152957938927640625 * (S3*S5*S19*Sq) := by ring
  have hmpos : 0 < m^2 := by rw [hfac]; positivity
  have hineq : 305565381020812367 * D * (m^2) ≤ 152957938927640625 * p * (m^2) := by
    have hmulD := Nat.mul_le_mul_left D hcross
    calc
      305565381020812367 * D * (m^2) = D * (305565381020812367 * (3^(2*a)*5^(2*b)*19^(2*c)*107^(2*e))) := by rw [hfac]; ring
      _ ≤ D * (152957938927640625 * (S3*S5*S19*Sq)) := hmulD
      _ = 152957938927640625 * (D*sigma) := by rw [hsigma]; ring
      _ = 152957938927640625 * (p*(m^2)) := by rw [hrel]
      _ = 152957938927640625 * p * (m^2) := by ring
  have hcoef : 305565381020812367 * D ≤ 152957938927640625 * p := by
    apply Nat.le_of_mul_le_mul_right (by simpa [Nat.mul_assoc] using hineq)
    exact hmpos
  have hD437 : 437 ≤ D := by
    by_contra hbad
    have hle : D ≤ 853 := by omega
    rw [hp_eq] at hcoef
    omega
  have hu3 := OddPerfectNumber.geom_sum_cross_lt_of_le 3 3 (2*a) (by norm_num) (by norm_num) (by norm_num)
  have hu5 := OddPerfectNumber.geom_sum_cross_lt_of_le 5 5 (2*b) (by norm_num) (by norm_num) (by norm_num)
  have hu19 := OddPerfectNumber.geom_sum_cross_lt_of_le 19 19 (2*c) (by norm_num) (by norm_num) (by norm_num)
  have huq := OddPerfectNumber.geom_sum_cross_lt_of_le 107 107 (2*e) (by norm_num) (by norm_num) (by norm_num)
  have hu35 := Nat.mul_lt_mul_of_lt_of_lt hu3 hu5
  have hu19q := Nat.mul_lt_mul_of_lt_of_lt hu19 huq
  have hu := Nat.mul_lt_mul_of_lt_of_lt hu35 hu19q
  norm_num at hu
  have hupper : 15264 * sigma < 30495 * (m^2) := by
    calc
      15264*sigma = (2*S3)*(4*S5)*(18*S19)*(106 * Sq) := by rw [hsigma]; dsimp [S3,S5,S19,Sq]; ring
      _ < (3*3^(2*a))*(5*5^(2*b))*((19*19^(2*c))*(107*107^(2*e))) := by simpa [S3,S5,S19,Sq, Nat.mul_assoc] using hu
      _ = 30495*(m^2) := by rw [hfac]; ring
  have hineqU : 15264*p*(m^2) < 30495*D*(m^2) := by
    calc
      15264*p*(m^2) = 15264*(p*(m^2)) := by ring
      _ = 15264*(D*sigma) := by rw [hrel]
      _ = D*(15264*sigma) := by ring
      _ < D*(30495*(m^2)) := (Nat.mul_lt_mul_left (by omega)).2 hupper
      _ = 30495*D*(m^2) := by ring
  have hcoefU : 15264*p < 30495*D := by
    apply Nat.lt_of_mul_lt_mul_right (by simpa [Nat.mul_assoc] using hineqU)
  have hD462 : D ≤ 462 := by
    by_contra hbad
    have hge : 961 ≤ D := by omega
    rw [hp_eq] at hcoefU
    omega
  exact ⟨hD437, hD462⟩






