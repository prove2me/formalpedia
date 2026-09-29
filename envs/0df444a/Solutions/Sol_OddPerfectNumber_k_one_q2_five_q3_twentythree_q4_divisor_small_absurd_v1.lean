-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentythree_q4_divisor_small_absurd_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-16T07:47:10.341782+00:00
-- url     : https://prove2.me/submissions/2f3051f3-f921-4c60-bfa8-f1ed3a4b75ec

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_ten
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_six_sharp
import Theorems.Thm_OddPerfectNumber_geom_mul_sub_one
import Theorems.Thm_OddPerfectNumber_geom_sum_last_three_terms_le
import Theorems.Thm_OddPerfectNumber_geom_sum_not_dvd_of_even_order
import Theorems.Thm_OddPerfectNumber_even_orders_mod_157_q3_twentythree
import Theorems.Thm_OddPerfectNumber_even_orders_mod_193_q3_twentythree

theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hcases : (D = 31 ∧ q4 = 31) ∨ (D = 37 ∧ q4 = 37) ∨
      (D = 79 ∧ q4 = 79) ∨ (D = 87 ∧ q4 = 29) ∨ (D = 97 ∧ q4 = 97))
    (hp_eq : p = 2 * D - 1) (ha : 5 ≤ a) (hb : 3 ≤ b)
    (hc : 4 ≤ c) (he : 1 ≤ e) : False := by
  have hsmall : q4 ≤ 37 ∨ (D = 79 ∧ q4 = 79) ∨ (D = 97 ∧ q4 = 97) := by
    rcases hcases with h31 | h37 | h79 | h87 | h97
    · omega
    · omega
    · exact Or.inr (Or.inl h79)
    · omega
    · exact Or.inr (Or.inr h97)
  rcases hsmall with hqsmall | h79 | h97
  · let S3 := ∑ i ∈ Finset.range (2*a + 1), 3 ^ i
    let S5 := ∑ i ∈ Finset.range (2*b + 1), 5 ^ i
    let S23 := ∑ i ∈ Finset.range (2*c + 1), 23 ^ i
    let Sq := ∑ i ∈ Finset.range (2*e + 1), q4 ^ i
    have h3 := OddPerfectNumber.geom_ratio_lower_three_ge_ten (2*a) (by omega)
    have h5 := OddPerfectNumber.geom_ratio_lower_five_ge_six_sharp (2*b) (by omega)
    have hgeom := OddPerfectNumber.geom_mul_sub_one 23 (2*c + 1) (by norm_num)
    rw [pow_succ] at hgeom
    have hpow23 : 23 ^ 8 ≤ 23 ^ (2*c) := by
      exact Nat.pow_le_pow_right (by norm_num : 0 < 23) (by omega)
    have h23 : 81870575521 * 23 ^ (2*c) ≤ 78310985281 * S23 := by
      dsimp [S23]
      omega
    have hlast := OddPerfectNumber.geom_sum_last_three_terms_le q4 (2*e) (by omega)
    have hpow1 : q4^(2*e) = q4^2 * q4^(2*e-2) := by
      calc
        q4^(2*e) = q4^((2*e-2)+2) := by congr 1 <;> omega
        _ = q4^2 * q4^(2*e-2) := by rw [pow_add]; ring
    have hqpoly : (q4^2 + q4 + 1) * q4^(2*e-2) ≤ Sq := by
      dsimp [Sq] at hlast ⊢
      calc
        (q4^2 + q4 + 1) * q4^(2*e-2) =
            q4^2 * q4^(2*e-2) + q4 * q4^(2*e-2) + q4^(2*e-2) := by ring
        _ = q4^2 * q4^(2*e-2) + q4^1 * q4^(2*e-2) + q4^(2*e-2) := by norm_num
        _ = q4^(2 + (2*e-2)) + q4^(1 + (2*e-2)) + q4^(2*e-2) := by
          rw [← pow_add, ← pow_add]
        _ = q4^(2*e) + q4^(2*e-1) + q4^(2*e-2) := by
          have he1 : 2 + (2*e-2) = 2*e := by omega
          have he2 : 1 + (2*e-2) = 2*e-1 := by omega
          rw [he1, he2]
        _ ≤ ∑ i ∈ Finset.range (2*e + 1), q4^i := hlast
    have hq2 : q4 * q4 ≤ 37 * q4 := Nat.mul_le_mul_right q4 hqsmall
    have hq2' : 153 * (q4 * q4) ≤ 153 * (37 * q4) :=
      Nat.mul_le_mul_left 153 hq2
    have hqcoef : 5778 * (q4 * q4) ≤ 5625 * (q4 * q4 + q4 + 1) := by
      calc
        5778 * (q4*q4) = 5625 * (q4*q4) + 153 * (q4*q4) := by ring
        _ ≤ 5625 * (q4*q4) + 153 * (37*q4) := Nat.add_le_add_left hq2' _
        _ ≤ 5625 * (q4*q4 + q4 + 1) := by omega
    have hq : 5778 * q4^(2*e) ≤ 5625 * Sq := by
      have hqpoly' : (q4*q4 + q4 + 1) * q4^(2*e-2) ≤ Sq := by
        simpa [pow_two] using hqpoly
      calc
        5778 * q4^(2*e) = 5778 * ((q4*q4) * q4^(2*e-2)) := by rw [hpow1]; ring
        _ ≤ 5625 * ((q4*q4 + q4 + 1) * q4^(2*e-2)) := by
          have ht := Nat.mul_le_mul_right (q4^(2*e-2)) hqcoef
          simpa [Nat.mul_assoc] using ht
        _ ≤ 5625 * Sq := Nat.mul_le_mul_left 5625 hqpoly'
    have hmul35 := Nat.mul_le_mul h3 h5
    have h23q := Nat.mul_le_mul h23 hq
    have hmul := Nat.mul_le_mul hmul35 h23q
    have hcross :
        818335168182043302390894 *
            (3^(2*a) * 5^(2*b) * 23^(2*c) * q4^(2*e)) ≤
          406422542272655478515625 * (S3 * S5 * S23 * Sq) := by
      calc
        818335168182043302390894 *
            (3^(2*a) * 5^(2*b) * 23^(2*c) * q4^(2*e)) =
            (88573*3^(2*a)) * (19531*5^(2*b)) *
              ((81870575521*23^(2*c)) * (5778*q4^(2*e))) := by ring
        _ ≤ (59049*S3) * (15625*S5) *
              ((78310985281*S23) * (5625*Sq)) := by
          simpa only [S3, S5, S23, Sq] using hmul
        _ = 406422542272655478515625 * (S3*S5*S23*Sq) := by ring
    have hq4pos : 0 < q4 := by
      rcases hcases with h31 | h37 | h79' | h87 | h97'
      · omega
      · omega
      · omega
      · omega
      · omega
    have hmpos : 0 < m^2 := by rw [hfac]; positivity
    have hineq :
        818335168182043302390894 * D * (m^2) ≤
          406422542272655478515625 * p * (m^2) := by
      have hmulD := Nat.mul_le_mul_left D hcross
      calc
        818335168182043302390894 * D * (m^2) =
            D * (818335168182043302390894 *
              (3^(2*a)*5^(2*b)*23^(2*c)*q4^(2*e))) := by rw [hfac]; ring
        _ ≤ D * (406422542272655478515625 * (S3*S5*S23*Sq)) := hmulD
        _ = 406422542272655478515625 * (D*sigma) := by rw [hsigma]; ring
        _ = 406422542272655478515625 * (p*(m^2)) := by rw [hrel]
        _ = 406422542272655478515625 * p * (m^2) := by ring
    have hconst : 406422542272655478515625 * p <
        818335168182043302390894 * D := by
      rcases hcases with h31 | h37 | h79 | h87 | h97
      · norm_num [h31.1, hp_eq]
      · norm_num [h37.1, hp_eq]
      · omega
      · norm_num [h87.1, hp_eq]
      · omega
    have hstrict :
        406422542272655478515625 * p * (m^2) <
          818335168182043302390894 * D * (m^2) :=
      Nat.mul_lt_mul_of_pos_right hconst hmpos
    exact False.elim ((Nat.not_lt_of_ge hineq) hstrict)
  · rcases h79 with ⟨hD, hq79eq⟩
    have hrel79 : 79 * sigma = 157 * m^2 := by
      calc
        79 * sigma = D * sigma := by rw [hD]
        _ = p * m^2 := hrel
        _ = 157 * m^2 := by norm_num [hp_eq, hD]
    have hdiv : 157 ∣ sigma := by
      have hdvd : 157 ∣ 79 * sigma := by
        refine ⟨m^2, ?_⟩
        exact hrel79
      exact (by norm_num : Nat.Coprime 157 79).dvd_of_dvd_mul_left hdvd
    have heven := OddPerfectNumber.even_orders_mod_157_q3_twentythree
    have hnot (x t : Nat) (hx : Even (orderOf (x : ZMod 157))) :
        ¬ 157 ∣ ∑ i ∈ Finset.range (2*t+1), x^i :=
      OddPerfectNumber.geom_sum_not_dvd_of_even_order hx
    rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 157)).mp (by simpa [hsigma] using hdiv) with hrest | hqsrc
    · rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 157)).mp hrest with hrest' | h23
      · rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 157)).mp hrest' with h3 | h5
        · exact False.elim ((hnot 3 a heven.1) h3)
        · exact False.elim ((hnot 5 b heven.2.1) h5)
      · exact False.elim ((hnot 23 c heven.2.2.1) h23)
    · have hq79 : 157 ∣ ∑ i ∈ Finset.range (2*e+1), 79^i := by simpa [hq79eq] using hqsrc
      exact False.elim ((hnot 79 e heven.2.2.2) hq79)
  · rcases h97 with ⟨hD, hq97eq⟩
    have hrel97 : 97 * sigma = 193 * m^2 := by
      calc
        97 * sigma = D * sigma := by rw [hD]
        _ = p * m^2 := hrel
        _ = 193 * m^2 := by norm_num [hp_eq, hD]
    have hdiv : 193 ∣ sigma := by
      have hdvd : 193 ∣ 97 * sigma := by
        refine ⟨m^2, ?_⟩
        exact hrel97
      exact (by norm_num : Nat.Coprime 193 97).dvd_of_dvd_mul_left hdvd
    have heven := OddPerfectNumber.even_orders_mod_193_q3_twentythree
    have hnot (x t : Nat) (hx : Even (orderOf (x : ZMod 193))) :
        ¬ 193 ∣ ∑ i ∈ Finset.range (2*t+1), x^i :=
      OddPerfectNumber.geom_sum_not_dvd_of_even_order hx
    rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 193)).mp (by simpa [hsigma] using hdiv) with hrest | hqsrc
    · rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 193)).mp hrest with hrest' | h23
      · rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 193)).mp hrest' with h3 | h5
        · exact False.elim ((hnot 3 a heven.1) h3)
        · exact False.elim ((hnot 5 b heven.2.1) h5)
      · exact False.elim ((hnot 23 c heven.2.2.1) h23)
    · have hq97 : 193 ∣ ∑ i ∈ Finset.range (2*e+1), 97^i := by simpa [hq97eq] using hqsrc
      exact False.elim ((hnot 97 e heven.2.2.2) hq97)
