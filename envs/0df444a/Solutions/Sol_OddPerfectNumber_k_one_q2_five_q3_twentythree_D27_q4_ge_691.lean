-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentythree_D27_q4_ge_691
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T15:12:10.509616+00:00
-- url     : https://prove2.me/submissions/935e6e18-6b37-4b33-b104-9813645e958a

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_mul_sub_one
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_ten
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_six_sharp
import Theorems.Thm_OddPerfectNumber_geom_sum_last_two_terms_le

theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hD : D = 27) (hp_eq : p = 2 * D - 1)
    (hq4prime : q4.Prime) (hq4gt : 23 < q4)
    (ha : 5 ≤ a) (hb : 3 ≤ b) (hc : 4 ≤ c) (he : 1 ≤ e) :
    691 ≤ q4 := by
  by_contra hbad
  have hqle : q4 ≤ 690 := by omega
  let S3 : Nat := ∑ i ∈ Finset.range (2*a + 1), 3 ^ i
  let S5 : Nat := ∑ i ∈ Finset.range (2*b + 1), 5 ^ i
  let S23 : Nat := ∑ i ∈ Finset.range (2*c + 1), 23 ^ i
  let Sq : Nat := ∑ i ∈ Finset.range (2*e + 1), q4 ^ i
  have h3 := OddPerfectNumber.geom_ratio_lower_three_ge_ten (2*a) (by omega)
  have h5 := OddPerfectNumber.geom_ratio_lower_five_ge_six_sharp (2*b) (by omega)
  have hgeom := OddPerfectNumber.geom_mul_sub_one 23 (2*c + 1) (by norm_num)
  rw [pow_succ] at hgeom
  have hpow23 : 23 ^ 8 ≤ 23 ^ (2*c) := by
    exact Nat.pow_le_pow_right (by norm_num : 0 < 23) (by omega)
  have h23 : 81870575521 * 23 ^ (2*c) ≤
      78310985281 * S23 := by
    dsimp [S23]
    omega
  have hlast := OddPerfectNumber.geom_sum_last_two_terms_le q4 (2*e) (by omega)
  have hpowq : q4 ^ (2*e) ≤ 690 * q4 ^ (2*e - 1) := by
    rw [show 2*e = (2*e - 1) + 1 by omega, pow_succ]
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left (q4 ^ (2*e - 1)) hqle
  have hlin : 691 * q4 ^ (2*e) ≤
      690 * q4 ^ (2*e) + 690 * q4 ^ (2*e - 1) := by omega
  have hq : 691 * q4 ^ (2*e) ≤ 690 * Sq := by
    calc
      691 * q4 ^ (2*e) ≤ 690 * q4 ^ (2*e) + 690 * q4 ^ (2*e - 1) := hlin
      _ = 690 * (q4 ^ (2*e) + q4 ^ (2*e - 1)) := by ring
      _ ≤ 690 * Sq := Nat.mul_le_mul_left 690 (by simpa [Sq] using hlast)
  have h35 := Nat.mul_le_mul h3 h5
  have h23q := Nat.mul_le_mul h23 hq
  have hmul := Nat.mul_le_mul h35 h23q
  have hcross :
      97865974595671845266893 *
          (3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e)) ≤
        49854498518779072031250 * (S3 * S5 * S23 * Sq) := by
    calc
      97865974595671845266893 *
          (3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e)) =
          (88573 * 3^(2*a)) * (19531 * 5^(2*b)) *
            ((81870575521 * 23^(2*c)) * (691 * q4^(2*e))) := by ring
      _ ≤ (59049 * S3) * (15625 * S5) *
            ((78310985281 * S23) * (690 * Sq)) := by
        simpa only [S3, S5, S23, Sq] using hmul
      _ = 49854498518779072031250 * (S3 * S5 * S23 * Sq) := by ring
  have hmpos : 0 < m ^ 2 := by
    rw [hfac]
    positivity
  have hineq :
      97865974595671845266893 * D * (m ^ 2) ≤
        49854498518779072031250 * p * (m ^ 2) := by
    have hmulD := Nat.mul_le_mul_left D hcross
    calc
      97865974595671845266893 * D * (m ^ 2) =
          D * (97865974595671845266893 *
            (3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e))) := by
              rw [hfac]
              ring
      _ ≤ D * (49854498518779072031250 * (S3 * S5 * S23 * Sq)) := hmulD
      _ = 49854498518779072031250 * (D * sigma) := by rw [hsigma]; ring
      _ = 49854498518779072031250 * (p * (m ^ 2)) := by rw [hrel]
      _ = 49854498518779072031250 * p * (m ^ 2) := by ring
  have hpval : p = 53 := by omega
  have hineq' :
      97865974595671845266893 * 27 * (m ^ 2) ≤
        49854498518779072031250 * 53 * (m ^ 2) := by
    simpa [hD, hpval] using hineq
  have hreverse :
      49854498518779072031250 * 53 * (m ^ 2) <
        97865974595671845266893 * 27 * (m ^ 2) := by
    have hc : 49854498518779072031250 * 53 <
        97865974595671845266893 * 27 := by norm_num
    exact Nat.mul_lt_mul_of_pos_right hc hmpos
  exact False.elim ((Nat.not_lt_of_ge hineq') hreverse)
