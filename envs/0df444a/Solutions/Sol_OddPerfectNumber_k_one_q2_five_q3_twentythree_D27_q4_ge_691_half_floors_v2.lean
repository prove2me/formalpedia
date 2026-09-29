-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentythree_D27_q4_ge_691_half_floors_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-17T11:22:50.949784+00:00
-- url     : https://prove2.me/submissions/8472302d-35f4-4178-84a3-c098b232c763

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_mul_sub_one
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_eight
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_six_sharp
import Theorems.Thm_OddPerfectNumber_geom_sum_last_two_terms_le

-- EXPONENT CONVENTION: a,b,c,e are half exponents.
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
    (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) :
    691 ≤ q4 := by
  have hgt : 683 < q4 := by
    by_contra hbad
    have hqle : q4 ≤ 683 := by omega
    let S3 : Nat := ∑ i ∈ Finset.range (2*a + 1), 3 ^ i
    let S5 : Nat := ∑ i ∈ Finset.range (2*b + 1), 5 ^ i
    let S23 : Nat := ∑ i ∈ Finset.range (2*c + 1), 23 ^ i
    let Sq : Nat := ∑ i ∈ Finset.range (2*e + 1), q4 ^ i
    have h3 := OddPerfectNumber.geom_ratio_lower_three_ge_eight (2*a) (by omega)
    have h5 := OddPerfectNumber.geom_ratio_lower_five_ge_six_sharp (2*b) (by omega)
    have hgeom := OddPerfectNumber.geom_mul_sub_one 23 (2*c + 1) (by norm_num)
    rw [pow_succ] at hgeom
    have hpow23 : 23 ^ 4 ≤ 23 ^ (2*c) := by
      exact Nat.pow_le_pow_right (by norm_num : 0 < 23) (by omega)
    have h23 : 292561 * 23 ^ (2*c) ≤ 279841 * S23 := by
      dsimp [S23]
      omega
    have hlast := OddPerfectNumber.geom_sum_last_two_terms_le q4 (2*e) (by omega)
    have hpowq : q4 ^ (2*e) ≤ 683 * q4 ^ (2*e - 1) := by
      rw [show 2*e = (2*e - 1) + 1 by omega, pow_succ]
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left (q4 ^ (2*e - 1)) hqle
    have hlin : 684 * q4 ^ (2*e) ≤
        683 * q4 ^ (2*e) + 683 * q4 ^ (2*e - 1) := by omega
    have hq : 684 * q4 ^ (2*e) ≤ 683 * Sq := by
      calc
        684 * q4 ^ (2*e) ≤ 683 * q4 ^ (2*e) + 683 * q4 ^ (2*e - 1) := hlin
        _ = 683 * (q4 ^ (2*e) + q4 ^ (2*e - 1)) := by ring
        _ ≤ 683 * Sq := Nat.mul_le_mul_left 683 (by simpa [Sq] using hlast)
    have hmul := Nat.mul_le_mul (Nat.mul_le_mul h3 h5) (Nat.mul_le_mul h23 hq)
    have hcross :
        38462388063490404 *
            (3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e)) ≤
          19593955235671875 * (S3 * S5 * S23 * Sq) := by
      calc
        38462388063490404 *
            (3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e)) =
            (9841 * 3^(2*a)) * (19531 * 5^(2*b)) *
              ((292561 * 23^(2*c)) * (684 * q4^(2*e))) := by ring
        _ ≤ (6561 * S3) * (15625 * S5) *
              ((279841 * S23) * (683 * Sq)) := by
            simpa only [S3, S5, S23, Sq] using hmul
        _ = 19593955235671875 * (S3 * S5 * S23 * Sq) := by ring
    have hmpos : 0 < m ^ 2 := by
      rw [hfac]
      positivity
    have hineq :
        38462388063490404 * D * (m ^ 2) ≤
          19593955235671875 * p * (m ^ 2) := by
      have hmulD := Nat.mul_le_mul_left D hcross
      calc
        38462388063490404 * D * (m ^ 2) =
            D * (38462388063490404 *
              (3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e))) := by
                rw [hfac]
                ring
        _ ≤ D * (19593955235671875 * (S3 * S5 * S23 * Sq)) := hmulD
        _ = 19593955235671875 * (D * sigma) := by rw [hsigma]; ring
        _ = 19593955235671875 * (p * (m ^ 2)) := by rw [hrel]
        _ = 19593955235671875 * p * (m ^ 2) := by ring
    have hpval : p = 53 := by omega
    have hineq' :
        38462388063490404 * 27 * (m ^ 2) ≤
          19593955235671875 * 53 * (m ^ 2) := by
      simpa [hD, hpval] using hineq
    have hreverse :
        19593955235671875 * 53 * (m ^ 2) <
          38462388063490404 * 27 * (m ^ 2) := by
      have hcoef : 19593955235671875 * 53 < 38462388063490404 * 27 := by norm_num
      exact Nat.mul_lt_mul_of_pos_right hcoef hmpos
    exact (Nat.not_lt_of_ge hineq') hreverse
  by_contra hbad
  have hle : q4 ≤ 690 := by omega
  interval_cases q4 <;> norm_num at hq4prime
