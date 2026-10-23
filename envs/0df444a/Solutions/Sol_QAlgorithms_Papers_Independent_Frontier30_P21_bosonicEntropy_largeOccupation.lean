-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier30.P21.bosonicEntropy_largeOccupation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:01:33.998704+00:00
-- url     : https://prove2.me/submissions/74ac76be-a435-4a22-8d10-8e12ce74b20d

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P21

open Filter Topology QAlgorithms.Papers.Independent.Frontier30.P21

theorem solution :
    Tendsto (fun x : ℝ => bosonicEntropy x / Real.logb 2 x) atTop (nhds 1) := by
  have hlog : Tendsto (fun x : ℝ => 1 + 2 * (Real.log x)⁻¹) atTop (nhds 1) := by
    have := (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).const_mul 2
    simpa using this.const_add 1
  have key : ∀ x : ℝ, 1 < x →
      1 ≤ bosonicEntropy x / Real.logb 2 x ∧
        bosonicEntropy x / Real.logb 2 x ≤ 1 + 2 * (Real.log x)⁻¹ := by
    intro x hx
    have hx0 : 0 < x := by linarith
    have hL : 0 < Real.log x := Real.log_pos hx
    have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hr : bosonicEntropy x / Real.logb 2 x =
        (Real.log (x + 1) + x * (Real.log (x + 1) - Real.log x)) / Real.log x := by
      unfold bosonicEntropy Real.logb
      field_simp
      ring
    -- 0 ≤ log(x+1) - log x ≤ 1/x
    have hd0 : Real.log x ≤ Real.log (x + 1) := Real.log_le_log hx0 (by linarith)
    have hd1 : Real.log (x + 1) - Real.log x ≤ 1 / x := by
      rw [← Real.log_div (by linarith) hx0.ne']
      have := Real.log_le_sub_one_of_pos (show 0 < (x + 1) / x by positivity)
      have e : (x + 1) / x - 1 = 1 / x := by field_simp; ring
      linarith
    have hxd : x * (Real.log (x + 1) - Real.log x) ≤ 1 := by
      have := mul_le_mul_of_nonneg_left hd1 hx0.le
      rwa [mul_one_div_cancel hx0.ne'] at this
    have hxd0 : 0 ≤ x * (Real.log (x + 1) - Real.log x) :=
      mul_nonneg hx0.le (by linarith)
    have h1x : 1 / x ≤ 1 := by rw [div_le_one hx0]; linarith
    rw [hr]
    constructor
    · rw [le_div_iff₀ hL]; linarith
    · rw [div_le_iff₀ hL, add_mul, inv_mul_cancel_right₀ hL.ne' 2]
      nlinarith
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlog ?_ ?_
  · filter_upwards [eventually_gt_atTop 1] with x hx using (key x hx).1
  · filter_upwards [eventually_gt_atTop 1] with x hx using (key x hx).2
