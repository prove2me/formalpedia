-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P31.elementaryLogarithmic_estimate
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T08:17:17.48271+00:00
-- url     : https://prove2.me/submissions/22542fef-03b6-41c2-ac98-37986ca9224a

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P31
noncomputable section

open QAlgorithms.Papers.Independent.Claimed50.P31

open scoped ENNReal ComplexOrder


theorem solution (x : ℝ) (hx : 0 < x) (hxHalf : x ≤ 1 / 2) :
    1 / (2 - Real.logb 2 x) ^ 2 ≥ (Real.exp 3 * (Real.log 2) ^ 2 / 54) * x := by
  set L := Real.log x with hL
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLle : L ≤ -Real.log 2 := by
    rw [hL, ← Real.log_inv]
    exact Real.log_le_log hx (by norm_num at hxHalf ⊢; linarith)
  set s := 2 * Real.log 2 - L with hs
  have hs0 : 0 < s := by linarith
  have hlogb : 2 - Real.logb 2 x = s / Real.log 2 := by
    rw [Real.logb, hs]; field_simp; ring
  have hxe : x = Real.exp (2 * Real.log 2 - s) := by
    rw [hs, sub_sub_cancel, hL, Real.exp_log hx]
  have hexp2 : Real.exp (2 * Real.log 2 - s) = 4 * Real.exp (-s) := by
    rw [sub_eq_add_neg, Real.exp_add, show 2 * Real.log 2 = Real.log 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num, Real.exp_log (by norm_num)]
  -- s ≤ 2 exp(s/2 - 1)
  have hk : s / 2 ≤ Real.exp (s / 2 - 1) := by
    have := Real.add_one_le_exp (s / 2 - 1); linarith
  have hk2 : s ^ 2 ≤ 4 * Real.exp (s - 2) := by
    have h1 : Real.exp (s - 2) = Real.exp (s / 2 - 1) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [h1]
    nlinarith [hk, sq_nonneg (s / 2)]
  have he : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  set E := Real.exp (s - 3) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hs2 : Real.exp (s - 2) = Real.exp 1 * E := by
    rw [hE, ← Real.exp_add]; congr 1; ring
  have h3s : Real.exp 3 * Real.exp (-s) = E⁻¹ := by
    rw [hE, ← Real.exp_add, ← Real.exp_neg]; congr 1; ring
  have key : 4 * s ^ 2 ≤ 54 * E := by
    have : 4 * s ^ 2 ≤ 16 * (Real.exp 1 * E) := by rw [← hs2]; linarith
    nlinarith
  rw [hlogb, hxe, hexp2, ge_iff_le]
  have hrhs : Real.exp 3 * Real.log 2 ^ 2 / 54 * (4 * Real.exp (-s)) =
      4 * Real.log 2 ^ 2 / 54 * (Real.exp 3 * Real.exp (-s)) := by ring
  rw [hrhs, h3s, div_pow, one_div_div]
  rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
  rw [show 4 * Real.log 2 ^ 2 * E⁻¹ * s ^ 2 = (4 * s ^ 2) * E⁻¹ * Real.log 2 ^ 2 by ring]
  have : (4 * s ^ 2) * E⁻¹ ≤ 54 := by
    rw [mul_inv_le_iff₀ hE0]; linarith
  nlinarith [sq_nonneg (Real.log 2)]

end
