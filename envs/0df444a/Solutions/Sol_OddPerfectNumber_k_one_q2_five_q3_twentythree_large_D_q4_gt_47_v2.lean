-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentythree_large_D_q4_gt_47_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-16T08:49:08.905463+00:00
-- url     : https://prove2.me/submissions/8c1546cf-daa4-4da8-8437-e15a4300960a

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_ten
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_six_sharp
import Theorems.Thm_OddPerfectNumber_geom_mul_sub_one
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_base_le47

theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2) (hDlow : 111 ≤ D)
    (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime)
    (hq4gt : 23 < q4) (hq4le : q4 ≤ 47) (ha : 5 ≤ a)
    (hb : 3 ≤ b) (hc : 4 ≤ c) (he : 1 ≤ e) : False := by
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
  have h23 : 81870575521 * 23 ^ (2*c) ≤ 78310985281 * S23 := by
    dsimp [S23]
    omega
  have hq := OddPerfectNumber.geom_ratio_lower_base_le47 q4 (2*e) (by omega) (by omega)
  have hmul := Nat.mul_le_mul (Nat.mul_le_mul h3 h5) (Nat.mul_le_mul h23 hq)
  have hcross :
      6798215312000359729104 *
          (3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e)) ≤
        3395886130989299109375 * (S3 * S5 * S23 * Sq) := by
    calc
      6798215312000359729104 *
          (3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e)) =
          (88573 * 3^(2*a)) * (19531 * 5^(2*b)) *
            ((81870575521 * 23^(2*c)) * (48*q4^(2*e))) := by ring
      _ ≤ (59049*S3) * (15625*S5) *
            ((78310985281*S23) * (47*Sq)) := by
        simpa only [S3, S5, S23, Sq] using hmul
      _ = 3395886130989299109375 * (S3*S5*S23*Sq) := by ring
  have hmpos : 0 < m ^ 2 := by rw [hfac]; positivity
  have hineq :
      6798215312000359729104 * D * (m ^ 2) ≤
        3395886130989299109375 * p * (m ^ 2) := by
    have hmulD := Nat.mul_le_mul_left D hcross
    calc
      6798215312000359729104 * D * (m ^ 2) =
          D * (6798215312000359729104 *
            (3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e))) := by
              rw [hfac]
              ring
      _ ≤ D * (3395886130989299109375 * (S3*S5*S23*Sq)) := hmulD
      _ = 3395886130989299109375 * (D * sigma) := by rw [hsigma]; ring
      _ = 3395886130989299109375 * (p * (m ^ 2)) := by rw [hrel]
      _ = 3395886130989299109375 * p * (m ^ 2) := by ring
  have hcancel :
      6798215312000359729104 * D ≤
        3395886130989299109375 * p :=
    Nat.le_of_mul_le_mul_right hineq hmpos
  rw [hp_eq] at hcancel
  norm_num at hcancel
  omega
