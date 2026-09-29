-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentythree_large_D_gt_47_half_floors_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-17T12:37:39.991983+00:00
-- url     : https://prove2.me/submissions/c0507afc-e79c-448b-a870-6cdb941a2632

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_eight
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_six_sharp
import Theorems.Thm_OddPerfectNumber_geom_mul_sub_one
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_base_le47

-- EXPONENT CONVENTION: a,b,c,e are HALF exponents, full floors 8,6,4,2.
theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2) (hDpos : 0 < D) (hp_eq : p = 2 * D - 1)
    (hq4prime : q4.Prime) (hq4gt : 23 < q4)
    (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) :
    47 < q4 := by
  by_contra hbad
  have hq4le : q4 ≤ 47 := by omega
  let S3 : Nat := ∑ i ∈ Finset.range (2*a + 1), 3 ^ i
  let S5 : Nat := ∑ i ∈ Finset.range (2*b + 1), 5 ^ i
  let S23 : Nat := ∑ i ∈ Finset.range (2*c + 1), 23 ^ i
  let Sq : Nat := ∑ i ∈ Finset.range (2*e + 1), q4 ^ i
  have h3 := OddPerfectNumber.geom_ratio_lower_three_ge_eight (2*a) (by omega)
  have h5 := OddPerfectNumber.geom_ratio_lower_five_ge_six_sharp (2*b) (by omega)
  have hgeom := OddPerfectNumber.geom_mul_sub_one 23 (2*c + 1) (by norm_num)
  rw [pow_succ] at hgeom
  have hpow23 : 23 ^ 4 ≤ 23 ^ (2*c) :=
    Nat.pow_le_pow_right (by norm_num : 0 < 23) (by omega)
  have h23 : 292561 * 23 ^ (2*c) ≤ 279841 * S23 := by
    dsimp [S23]
    omega
  have hq := OddPerfectNumber.geom_ratio_lower_base_le47 q4 (2*e) hq4le (by omega)
  have hmul := Nat.mul_le_mul (Nat.mul_le_mul h3 h5) (Nat.mul_le_mul h23 hq)
  have hcross : 2699114951823888 * m ^ 2 ≤ 1348339525734375 * sigma := by
    calc
      2699114951823888 * m ^ 2 =
          (9841 * 3^(2*a)) * (19531 * 5^(2*b)) *
            ((292561 * 23^(2*c)) * (48 * q4^(2*e))) := by rw [hfac]; ring
      _ ≤ (6561*S3) * (15625*S5) * ((279841*S23) * (47*Sq)) := by
        simpa only [S3, S5, S23, Sq] using hmul
      _ = 1348339525734375 * sigma := by rw [hsigma]; ring
  have hmpos : 0 < m ^ 2 := by rw [hfac]; positivity
  have hineq : (2699114951823888 * D) * m ^ 2 ≤
      (1348339525734375 * p) * m ^ 2 := by
    calc
      (2699114951823888 * D) * m ^ 2 = D * (2699114951823888 * m ^ 2) := by ring
      _ ≤ D * (1348339525734375 * sigma) := Nat.mul_le_mul_left D hcross
      _ = 1348339525734375 * (D * sigma) := by ring
      _ = 1348339525734375 * (p * m ^ 2) := by rw [hrel]
      _ = (1348339525734375 * p) * m ^ 2 := by ring
  have hcancel := Nat.le_of_mul_le_mul_right hineq hmpos
  omega
