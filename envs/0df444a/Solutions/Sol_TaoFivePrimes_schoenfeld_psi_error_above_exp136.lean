-- Prove2me | solution 1 for TaoFivePrimes.schoenfeld_psi_error_above_exp136
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T16:50:57.005212+00:00
-- url     : https://prove2.me/submissions/1d26cd42-243b-471c-824f-82b3a33f6759

import Mathlib
import Definitions.Def_dusart_psi_433_20261014_PsiComparison
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_PowerQuarterSmoothed
set_option autoImplicit false
set_option maxHeartbeats 1500000
open DusartSmoothing
namespace ExplicitPNT.DusartTable1

private theorem double_average_quarter_bound : ∀ (a h z : ℝ) (ha : 1 ≤ a) (hh : 0 < h)
    (haz : a + 2 * h ≤ z) (hT : 4 ≤ z / h),
    |doubleBoxAverage Chebyshev.psi a h - (a + h)| ≤
      2 + 192 * z^(9 / 8 : ℝ) / h^(1 / 4 : ℝ) + 512 * z^(3 / 2 : ℝ) / h^2 :=
  ExplicitPNT.DusartTable1.Modules.PowerQuarterSmoothed.2

private theorem exp_ten_lower : (1024 : ℝ) ≤ Real.exp 10 := by
  have he : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.exp_one_gt_d9
    norm_num at h
    linarith
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) he 10
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp
  exact hp

private theorem inflated_exp_rpow (t r : ℝ) (hr : r ≤ 2) :
    ((11 / 10 : ℝ) * Real.exp t)^r ≤ (5 / 4 : ℝ) * Real.exp (t * r) := by
  rw [Real.mul_rpow (by norm_num) (Real.exp_pos t).le, ← Real.exp_mul]
  have hc := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 11 / 10) hr
  norm_num at hc
  exact mul_le_mul_of_nonneg_right (hc.trans (by norm_num)) (Real.exp_pos _).le

private theorem psi_exp_power_bound (t : ℝ) (ht : 100 ≤ t) :
    |Chebyshev.psi (Real.exp t) - Real.exp t| ≤ 140 * Real.exp (9 * t / 10) := by
  let x := Real.exp t
  let y := Real.exp (9 * t / 10)
  let h := 16 * y
  let z := (11 / 10 : ℝ) * x
  have hx0 : 0 < x := Real.exp_pos _
  have hy0 : 0 < y := Real.exp_pos _
  have hh : 0 < h := mul_pos (by norm_num) hy0
  have hd : (1024 : ℝ) ≤ Real.exp (t / 10) :=
    exp_ten_lower.trans (Real.exp_le_exp.mpr (by linarith))
  have hs : x = y * Real.exp (t / 10) := by
    dsimp [x, y]
    rw [← Real.exp_add]
    congr 1
    ring
  have hsmall : h ≤ x / 20 := by
    dsimp [h]
    rw [hs]
    nlinarith [mul_le_mul_of_nonneg_left hd hy0.le]
  have hx2 : 2 ≤ x := by
    have he := exp_ten_lower.trans (Real.exp_le_exp.mpr (show 10 ≤ t by linarith))
    linarith
  have hy2 : 2 ≤ y := by
    have he := exp_ten_lower.trans (Real.exp_le_exp.mpr (show 10 ≤ 9 * t / 10 by linarith))
    exact (by linarith : (2 : ℝ) ≤ Real.exp (9 * t / 10))
  have hlow : 1 ≤ x - 2 * h := by linarith
  have hT : 4 ≤ z / h := (le_div_iff₀ hh).2 (by dsimp [z]; linarith)
  have hzlow : x - 2 * h + 2 * h ≤ z := by dsimp [z]; linarith
  have hzhigh : x + 2 * h ≤ z := by dsimp [z]; linarith
  have hroot : h^(1 / 4 : ℝ) = 2 * Real.exp (9 * t / 40) := by
    dsimp [h, y]
    rw [Real.mul_rpow (by norm_num) (Real.exp_pos _).le, ← Real.exp_mul]
    have h16 : (16 : ℝ)^(1 / 4 : ℝ) = 2 := by
      rw [show (16 : ℝ) = (2 : ℝ)^4 by norm_num, ← Real.rpow_natCast_mul (by norm_num)]
      norm_num
    rw [h16]
    congr 2
    ring
  have hsq : h^2 = 256 * Real.exp (9 * t / 5) := by
    dsimp [h, y]
    rw [mul_pow, ← Real.exp_nat_mul]
    norm_num
    ring_nf
  have hzero : 192 * z^(9 / 8 : ℝ) / h^(1 / 4 : ℝ) ≤ 120 * y := by
    apply (div_le_iff₀ (Real.rpow_pos_of_pos hh _)).2
    have hzpow := inflated_exp_rpow t (9 / 8) (by norm_num)
    change z^(9 / 8 : ℝ) ≤ (5 / 4 : ℝ) * Real.exp (t * (9 / 8)) at hzpow
    calc
      _ ≤ 192 * ((5 / 4 : ℝ) * Real.exp (t * (9 / 8))) :=
        mul_le_mul_of_nonneg_left hzpow (by norm_num)
      _ = 120 * y * h^(1 / 4 : ℝ) := by
        rw [hroot]
        dsimp [y]
        rw [show 120 * Real.exp (9 * t / 10) * (2 * Real.exp (9 * t / 40)) =
          240 * (Real.exp (9 * t / 10) * Real.exp (9 * t / 40)) by ring, ← Real.exp_add]
        rw [show 9 * t / 10 + 9 * t / 40 = t * (9 / 8) by ring]
        ring
  have hrest : 512 * z^(3 / 2 : ℝ) / h^2 ≤ y := by
    apply (div_le_iff₀ (sq_pos_of_pos hh)).2
    have hzpow := inflated_exp_rpow t (3 / 2) (by norm_num)
    change z^(3 / 2 : ℝ) ≤ (5 / 4 : ℝ) * Real.exp (t * (3 / 2)) at hzpow
    have he : (3 : ℝ) ≤ Real.exp (6 * t / 5) :=
      (by norm_num : (3 : ℝ) ≤ 1024).trans
        (exp_ten_lower.trans (Real.exp_le_exp.mpr (by linarith)))
    have hp := mul_le_mul_of_nonneg_left he (Real.exp_pos (t * (3 / 2))).le
    rw [← Real.exp_add] at hp
    have hprod : y * h^2 = 256 * Real.exp (t * (3 / 2) + 6 * t / 5) := by
      rw [hsq]
      dsimp [y]
      rw [show Real.exp (9 * t / 10) * (256 * Real.exp (9 * t / 5)) =
        256 * (Real.exp (9 * t / 10) * Real.exp (9 * t / 5)) by ring, ← Real.exp_add]
      congr 1
      ring
    rw [hprod]
    nlinarith [Real.exp_pos (t * (3 / 2))]
  have hbound : 2 + 192 * z^(9 / 8 : ℝ) / h^(1 / 4 : ℝ) +
      512 * z^(3 / 2 : ℝ) / h^2 ≤ 124 * y := by linarith
  have hl := (double_average_quarter_bound (x - 2 * h) h z hlow hh hzlow hT).trans hbound
  have hu := (double_average_quarter_bound x h z (by linarith) hh hzhigh hT).trans hbound
  have hcenter : x - 2 * h + h = x - h := by ring
  rw [hcenter] at hl
  have hp := psi_error_of_double_average_errors x h (124 * y) hh hl hu
  change |Chebyshev.psi x - x| ≤ 140 * y
  dsimp [h] at hp
  linarith

end ExplicitPNT.DusartTable1

private lemma exp_thirteen_point_six : (780000 : ℝ) ≤ Real.exp (68 / 5) := by
  have h13 : (442000 : ℝ) ≤ Real.exp 13 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283) Real.exp_one_gt_d9.le 13
    rw [← Real.exp_nat_mul] at hp
    norm_num at hp ⊢
    linarith
  have h06 : (89 / 50 : ℝ) ≤ Real.exp (3 / 5) := by
    have h := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 3/5 by norm_num) 3
    norm_num [Finset.sum_range_succ] at h
    exact h
  have hp := mul_le_mul h13 h06 (by norm_num : (0:ℝ) ≤ 89/50) (Real.exp_nonneg 13)
  have he : Real.exp 13 * Real.exp (3 / 5) = Real.exp (68 / 5) := by
    rw [← Real.exp_add]
    congr 1 <;> ring
  rw [he] at hp
  linarith

private lemma large_exp_dominates (t : ℝ) (ht : 136 ≤ t) :
    5600 * t ≤ Real.exp (t / 10) := by
  have hlin : 1 + (t - 136) / 10 ≤ Real.exp ((t - 136) / 10) := by
    linarith [Real.add_one_le_exp ((t - 136) / 10)]
  have hlin0 : 0 ≤ 1 + (t - 136) / 10 := by linarith
  have hp := mul_le_mul exp_thirteen_point_six hlin hlin0 (Real.exp_nonneg (68/5))
  have he : Real.exp (68 / 5) * Real.exp ((t - 136) / 10) = Real.exp (t / 10) := by
    rw [← Real.exp_add]
    congr 1 <;> ring
  rw [he] at hp
  nlinarith only [ht, hp]

theorem solution (y : ℝ) (hy : Real.exp 136 ≤ y) :
    |Chebyshev.psi y - y| ≤ y / (40 * Real.log y) := by
  have hypos : 0 < y := (Real.exp_pos 136).trans_le hy
  have ht : 136 ≤ Real.log y := by
    have hh := Real.log_le_log (Real.exp_pos 136) hy
    simpa using hh
  let t := Real.log y
  have hpsi := ExplicitPNT.DusartTable1.psi_exp_power_bound t (by dsimp [t]; linarith)
  have he : Real.exp t = y := Real.exp_log hypos
  have hbound : 140 * Real.exp (9*t/10) ≤ Real.exp t / (40*t) := by
    have ht0 : 0 < 40*t := by dsimp [t]; linarith
    apply (le_div_iff₀ ht0).2
    have hm := mul_le_mul_of_nonneg_left (large_exp_dominates t (by dsimp [t]; linarith))
      (Real.exp_nonneg (9*t/10))
    have heq : Real.exp (9*t/10) * Real.exp (t/10) = Real.exp t := by
      rw [← Real.exp_add]; congr 1 <;> ring
    rw [heq] at hm
    nlinarith only [hm]
  simpa [t, he] using hpsi.trans hbound
