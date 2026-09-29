-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_D45_canonical_absurd_v3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T08:54:41.32701+00:00
-- url     : https://prove2.me/submissions/29b19396-30ee-4ad6-a6c5-a8af56f3c371

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_eight
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_six_sharp
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_base_le47
import Theorems.Thm_OddPerfectNumber_geom_sum_last_two_terms_le
import Theorems.Thm_OddPerfectNumber_geom_sum_last_three_terms_le
import Theorems.Thm_OddPerfectNumber_geom_sum_cross_lt_of_le

theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hD : D = 45) (hp_eq : p = 2 * D - 1)
    (hq4 : q4.Prime) (hq4gt : 29 < q4)
    (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) : False := by
  let S3 := ∑ i ∈ Finset.range (2*a + 1), 3 ^ i
  let S5 := ∑ i ∈ Finset.range (2*b + 1), 5 ^ i
  let S29 := ∑ i ∈ Finset.range (2*c + 1), 29 ^ i
  let Sq := ∑ i ∈ Finset.range (2*e + 1), q4 ^ i
  have hi3 : 2 * S3 < 3 * 3 ^ (2*a) := by
    dsimp [S3]
    exact OddPerfectNumber.geom_sum_cross_lt_of_le 3 3 (2*a)
      (by norm_num) (by norm_num) (by norm_num)
  have hi5 : 4 * S5 < 5 * 5 ^ (2*b) := by
    dsimp [S5]
    exact OddPerfectNumber.geom_sum_cross_lt_of_le 5 5 (2*b)
      (by norm_num) (by norm_num) (by norm_num)
  have hi29 : 28 * S29 < 29 * 29 ^ (2*c) := by
    dsimp [S29]
    exact OddPerfectNumber.geom_sum_cross_lt_of_le 29 29 (2*c)
      (by norm_num) (by norm_num) (by norm_num)
  have hiq : (q4 - 1) * Sq < q4 * q4 ^ (2*e) := by
    dsimp [Sq]
    exact OddPerfectNumber.geom_sum_cross_lt_of_le q4 q4 (2*e)
      (by have := hq4.two_le; omega) (by omega) hq4
  have hmul12 := Nat.mul_lt_mul_of_lt_of_lt hi3 hi5
  have hmul123 := Nat.mul_lt_mul_of_lt_of_lt hmul12 hi29
  have hmul := Nat.mul_lt_mul_of_lt_of_lt hmul123 hiq
  have hupper : 224 * (q4 - 1) * sigma < 435 * q4 * m ^ 2 := by
    calc
      224 * (q4 - 1) * sigma =
          (2*S3) * (4*S5) * (28*S29) * ((q4-1)*Sq) := by
            rw [hsigma]
            dsimp [S3, S5, S29, Sq]
            ring
      _ < (3 * 3^(2*a)) * (5 * 5^(2*b)) *
          (29 * 29^(2*c)) * (q4 * q4^(2*e)) := by
            convert hmul using 1 <;> ring
      _ = 435 * q4 * m ^ 2 := by
            calc
              (3 * 3^(2*a)) * (5 * 5^(2*b)) *
                  (29 * 29^(2*c)) * (q4 * q4^(2*e)) =
                    435 * q4 *
                      (3^(2*a) * 5^(2*b) * 29^(2*c) * q4^(2*e)) := by ring
              _ = 435 * q4 * m ^ 2 := by rw [hfac]
  have hupperD := (Nat.mul_lt_mul_left (by omega : 0 < D)).2 hupper
  have hmpos : 0 < m ^ 2 := by
    rw [hfac]
    positivity
  have hconstmul :
      (224 * (q4 - 1) * p) * m ^ 2 <
        (435 * q4 * D) * m ^ 2 := by
    calc
      (224 * (q4 - 1) * p) * m ^ 2 =
          224 * (q4 - 1) * (p * m ^ 2) := by ring
      _ = 224 * (q4 - 1) * (D * sigma) := by rw [hrel]
      _ = D * (224 * (q4 - 1) * sigma) := by ring
      _ < D * (435 * q4 * m ^ 2) := hupperD
      _ = (435 * q4 * D) * m ^ 2 := by ring
  have hconst : 224 * (q4 - 1) * p < 435 * q4 * D := by
    exact (Nat.mul_lt_mul_right hmpos).mp hconstmul
  have hq4le55 : q4 ≤ 55 := by
    have hconst' : 224 * (q4 - 1) * 89 < 435 * q4 * 45 := by
      simpa [hD, hp_eq] using hconst
    norm_num at hconst'
    by_contra hnot
    have hq4ge : 56 ≤ q4 := by omega
    have hq4sub : q4 - 1 + 1 = q4 := by omega
    omega
  have hq4le : q4 ≤ 53 := by
    by_contra hnot
    have hq4lo : 54 ≤ q4 := by omega
    interval_cases q4 <;> norm_num at hq4
  have hq4cases : q4 ≤ 47 ∨ q4 = 53 := by
    by_cases hle : q4 ≤ 47
    · exact Or.inl hle
    · right
      have hq4lo : 48 ≤ q4 := by omega
      interval_cases q4 <;> norm_num at hq4 <;> norm_num
  rcases hq4cases with hq4le47 | rfl
  · have h3 := OddPerfectNumber.geom_ratio_lower_three_ge_eight (2*a) (by omega)
    have h5 := OddPerfectNumber.geom_ratio_lower_five_ge_six_sharp (2*b) (by omega)
    have h29 : 30 * 29^(2*c) ≤ 29 * S29 := by
      have hlast := OddPerfectNumber.geom_sum_last_two_terms_le 29 (2*c) (by omega)
      have hpow : 29^(2*c) = 29^(2*c - 1) * 29 := by
        calc
          29^(2*c) = 29^((2*c - 1) + 1) := by congr 1 <;> omega
          _ = 29^(2*c - 1) * 29 := by rw [pow_succ]
      calc
        30 * 29^(2*c) = 29 * (29^(2*c) + 29^(2*c - 1)) := by rw [hpow]; ring
        _ ≤ 29 * S29 := Nat.mul_le_mul_left 29 (by simpa [S29] using hlast)
    have hq := OddPerfectNumber.geom_ratio_lower_base_le47 q4 (2*e) hq4le47 (by omega)
    have hmul35 := Nat.mul_le_mul h3 h5
    have hmul29q := Nat.mul_le_mul h29 hq
    have hmul' := Nat.mul_le_mul hmul35 hmul29q
    have hcross :
        276774582240 * (3^(2*a) * 5^(2*b) * 29^(2*c) * q4^(2*e)) ≤
          139728796875 * (S3*S5*S29*Sq) := by
      calc
        276774582240 * (3^(2*a) * 5^(2*b) * 29^(2*c) * q4^(2*e)) =
            (9841*3^(2*a)) * (19531*5^(2*b)) *
              ((30*29^(2*c)) * (48*q4^(2*e))) := by ring
        _ ≤ (6561*S3) * (15625*S5) * ((29*S29) * (47*Sq)) := by
            simpa only [S3, S5, S29, Sq] using hmul'
        _ = 139728796875 * (S3*S5*S29*Sq) := by ring
    have hineq : 276774582240 * D * (m^2) ≤ 139728796875 * p * (m^2) := by
      have hmulD := Nat.mul_le_mul_left D hcross
      calc
        276774582240 * D * (m^2) =
            D * (276774582240 * (3^(2*a) * 5^(2*b) * 29^(2*c) * q4^(2*e))) := by rw [hfac]; ring
        _ ≤ D * (139728796875 * (S3*S5*S29*Sq)) := hmulD
        _ = 139728796875 * (D*sigma) := by rw [hsigma]; ring
        _ = 139728796875 * (p*(m^2)) := by rw [hrel]
        _ = 139728796875 * p * (m^2) := by ring
    have hstrict : 139728796875 * p < 276774582240 * D := by
      norm_num [hD, hp_eq]
    have := Nat.mul_lt_mul_of_pos_right hstrict hmpos
    exact False.elim ((Nat.not_lt_of_ge hineq) this)
  · have h3 := OddPerfectNumber.geom_ratio_lower_three_ge_eight (2*a) (by omega)
    have h5 := OddPerfectNumber.geom_ratio_lower_five_ge_six_sharp (2*b) (by omega)
    have h29 : (29*29 + 29 + 1) * 29^(2*c) ≤ (29*29) * S29 := by
      have hlast := OddPerfectNumber.geom_sum_last_three_terms_le 29 (2*c) (by omega)
      have hpow0 : 29^(2*c) = 29^(2*c - 2) * 29^2 := by
        calc
          29^(2*c) = 29^((2*c - 2) + 2) := by congr 1 <;> omega
          _ = 29^(2*c - 2) * 29^2 := by rw [pow_add]
      have hpow1 : 29^(2*c - 1) = 29^(2*c - 2) * 29 := by
        calc
          29^(2*c - 1) = 29^((2*c - 2) + 1) := by congr 1 <;> omega
          _ = 29^(2*c - 2) * 29 := by rw [pow_succ]
      calc
        (29*29 + 29 + 1) * 29^(2*c) =
            (29*29) * (29^(2*c) + 29^(2*c - 1) + 29^(2*c - 2)) := by rw [hpow0, hpow1]; ring
        _ ≤ (29*29) * S29 := Nat.mul_le_mul_left (29*29) (by simpa [S29] using hlast)
    have hq : (53*53 + 53 + 1) * 53^(2*e) ≤ (53*53) * Sq := by
      have hlast := OddPerfectNumber.geom_sum_last_three_terms_le 53 (2*e) (by omega)
      have hpow0 : 53^(2*e) = 53^(2*e - 2) * 53^2 := by
        calc
          53^(2*e) = 53^((2*e - 2) + 2) := by congr 1 <;> omega
          _ = 53^(2*e - 2) * 53^2 := by rw [pow_add]
      have hpow1 : 53^(2*e - 1) = 53^(2*e - 2) * 53 := by
        calc
          53^(2*e - 1) = 53^((2*e - 2) + 1) := by congr 1 <;> omega
          _ = 53^(2*e - 2) * 53 := by rw [pow_succ]
      calc
        (53*53 + 53 + 1) * 53^(2*e) =
            (53*53) * (53^(2*e) + 53^(2*e - 1) + 53^(2*e - 2)) := by rw [hpow0, hpow1]; ring
        _ ≤ (53*53) * Sq := Nat.mul_le_mul_left (53*53) (by simpa [Sq] using hlast)
    have hmul35 := Nat.mul_le_mul h3 h5
    have hmul29q := Nat.mul_le_mul h29 hq
    have hmul' := Nat.mul_le_mul hmul35 hmul29q
    have hcross :
        479295349179283 * (3^(2*a) * 5^(2*b) * 29^(2*c) * 53^(2*e)) ≤
          242179734515625 * (S3*S5*S29*Sq) := by
      calc
        479295349179283 * (3^(2*a) * 5^(2*b) * 29^(2*c) * 53^(2*e)) =
            (9841*3^(2*a)) * (19531*5^(2*b)) *
              (((29*29+29+1)*29^(2*c)) * ((53*53+53+1)*53^(2*e))) := by ring
        _ ≤ (6561*S3) * (15625*S5) * ((29*29*S29) * (53*53*Sq)) := by
            simpa only [S3, S5, S29, Sq] using hmul'
        _ = 242179734515625 * (S3*S5*S29*Sq) := by ring
    have hineq : 479295349179283 * D * (m^2) ≤ 242179734515625 * p * (m^2) := by
      have hmulD := Nat.mul_le_mul_left D hcross
      calc
        479295349179283 * D * (m^2) =
            D * (479295349179283 * (3^(2*a) * 5^(2*b) * 29^(2*c) * 53^(2*e))) := by rw [hfac]; ring
        _ ≤ D * (242179734515625 * (S3*S5*S29*Sq)) := hmulD
        _ = 242179734515625 * (D*sigma) := by rw [hsigma]; ring
        _ = 242179734515625 * (p*(m^2)) := by rw [hrel]
        _ = 242179734515625 * p * (m^2) := by ring
    have hstrict : 242179734515625 * p < 479295349179283 * D := by
      norm_num [hD, hp_eq]
    have := Nat.mul_lt_mul_of_pos_right hstrict hmpos
    exact False.elim ((Nat.not_lt_of_ge hineq) this)
