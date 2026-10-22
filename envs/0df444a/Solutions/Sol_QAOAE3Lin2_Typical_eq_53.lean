-- Prove2me | solution 1 for QAOAE3Lin2.Typical.eq_53
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:30:17.289734+00:00
-- url     : https://prove2.me/submissions/b35a9c4f-172f-460c-976d-6b981d36eede

import Mathlib
set_option autoImplicit false

open Filter Topology in
theorem solution :
    Filter.Tendsto
      (fun D : ℕ => Real.sqrt D *
        (Real.sin (1 / Real.sqrt (3 * D)) * Real.cos (1 / Real.sqrt (3 * D)) ^ (3 * D)))
      Filter.atTop (nhds (1 / Real.sqrt (3 * Real.exp 1))) := by
  -- the sine factor
  have hS : Tendsto (fun D : ℕ => Real.sqrt D * Real.sin (1 / Real.sqrt (3 * D))) atTop
      (𝓝 (1 / Real.sqrt 3)) := by
    have hlow : Tendsto (fun D : ℕ => 1 / Real.sqrt 3 * (1 - (1 / 18) / (D : ℝ))) atTop
        (𝓝 (1 / Real.sqrt 3)) := by
      have := (tendsto_const_div_atTop_nhds_zero_nat (1 / 18 : ℝ))
      have h2 := (tendsto_const_nhds (x := (1 : ℝ))).sub this
      have h3 := (tendsto_const_nhds (x := 1 / Real.sqrt 3)).mul h2
      simpa using h3
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with D hD
      have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
      have hDp : 0 < (D : ℝ) := by linarith
      set x : ℝ := 1 / Real.sqrt (3 * D) with hx
      have hs3 : 0 < Real.sqrt (3 * (D : ℝ)) := Real.sqrt_pos.mpr (by positivity)
      have hxpos : 0 < x := by positivity
      have hx2 : x ^ 2 = 1 / (3 * D) := by
        rw [hx, div_pow, Real.sq_sqrt (by positivity)]; simp
      have hDx : Real.sqrt D * x = 1 / Real.sqrt 3 := by
        rw [hx, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3)]
        have : 0 < Real.sqrt D := Real.sqrt_pos.mpr hDp
        have : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
        field_simp
      have hsin := Real.sin_gt_sub_cube hxpos
      have e : 1 / Real.sqrt 3 * (1 - (1 / 18) / (D : ℝ)) = Real.sqrt D * (x - x ^ 3 / 6) := by
        have : x - x ^ 3 / 6 = x * (1 - x ^ 2 / 6) := by ring
        rw [this, ← mul_assoc, hDx, hx2]
        congr 1
        field_simp
        ring
      rw [e]
      exact mul_le_mul_of_nonneg_left hsin.le (Real.sqrt_nonneg _)
    · filter_upwards [eventually_ge_atTop 1] with D hD
      have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
      have hDp : 0 < (D : ℝ) := by linarith
      set x : ℝ := 1 / Real.sqrt (3 * D) with hx
      have hs3 : 0 < Real.sqrt (3 * (D : ℝ)) := Real.sqrt_pos.mpr (by positivity)
      have hxpos : 0 < x := by positivity
      have hDx : Real.sqrt D * x = 1 / Real.sqrt 3 := by
        rw [hx, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3)]
        have : 0 < Real.sqrt D := Real.sqrt_pos.mpr hDp
        have : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
        field_simp
      rw [← hDx]
      exact mul_le_mul_of_nonneg_left (Real.sin_lt hxpos).le (Real.sqrt_nonneg _)
  -- the cosine factor
  have hg : Tendsto (fun n : ℕ => (n : ℝ) * (Real.cos (1 / Real.sqrt n) - 1)) atTop
      (𝓝 (-1 / 2)) := by
    have hup : Tendsto (fun n : ℕ => -1 / 2 + (5 / 96) / (n : ℝ)) atTop (𝓝 (-1 / 2)) := by
      have := (tendsto_const_div_atTop_nhds_zero_nat (5 / 96 : ℝ))
      simpa using (tendsto_const_nhds (x := (-1 / 2 : ℝ))).add this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hnp : 0 < (n : ℝ) := by linarith
      have hx2 : (1 / Real.sqrt n) ^ 2 = 1 / n := by
        rw [div_pow, Real.sq_sqrt hnp.le]; simp
      have h := Real.one_sub_sq_div_two_le_cos (x := 1 / Real.sqrt n)
      rw [hx2] at h
      have : -1 / 2 ≤ (n : ℝ) * (Real.cos (1 / Real.sqrt n) - 1) := by
        have h' : -(1 / (n : ℝ)) / 2 ≤ Real.cos (1 / Real.sqrt n) - 1 := by linarith
        have := mul_le_mul_of_nonneg_left h' hnp.le
        have e : (n : ℝ) * (-(1 / (n : ℝ)) / 2) = -1 / 2 := by field_simp
        linarith
      exact this
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hnp : 0 < (n : ℝ) := by linarith
      have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnp
      have hx2 : (1 / Real.sqrt n) ^ 2 = 1 / n := by
        rw [div_pow, Real.sq_sqrt hnp.le]; simp
      have hxle : |1 / Real.sqrt n| ≤ 1 := by
        rw [abs_of_pos (by positivity)]
        have : 1 ≤ Real.sqrt n := by
          rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hn'
        rw [div_le_one hsq]; exact this
      have h := Real.cos_bound hxle
      rw [abs_of_pos (by positivity : 0 < 1 / Real.sqrt n)] at h
      have h4 : (1 / Real.sqrt n) ^ 4 = 1 / (n : ℝ) ^ 2 := by
        have : (1 / Real.sqrt n) ^ 4 = ((1 / Real.sqrt n) ^ 2) ^ 2 := by ring
        rw [this, hx2]; field_simp
      rw [h4, hx2] at h
      have h' := (abs_le.mp h).2
      have h'' : Real.cos (1 / Real.sqrt n) - 1 ≤ -(1 / (n : ℝ)) / 2 + 1 / (n : ℝ) ^ 2 * (5 / 96) := by
        linarith
      have := mul_le_mul_of_nonneg_left h'' hnp.le
      have e : (n : ℝ) * (-(1 / (n : ℝ)) / 2 + 1 / (n : ℝ) ^ 2 * (5 / 96)) = -1 / 2 + (5 / 96) / n := by
        field_simp
      linarith
  have hC1 := Real.tendsto_one_add_pow_exp_of_tendsto hg
  have hC : Tendsto (fun D : ℕ => Real.cos (1 / Real.sqrt (3 * D)) ^ (3 * D)) atTop
      (𝓝 (Real.exp (-1 / 2))) := by
    have h3 : Tendsto (fun D : ℕ => 3 * D) atTop atTop :=
      tendsto_atTop_mono (fun n => (by show n ≤ 3 * n; omega)) tendsto_id
    have := hC1.comp h3
    refine this.congr (fun D => ?_)
    simp
  have hprod := hS.mul hC
  have hlim : 1 / Real.sqrt 3 * Real.exp (-1 / 2) = 1 / Real.sqrt (3 * Real.exp 1) := by
    have h1 : Real.exp (-1 / 2) = 1 / Real.sqrt (Real.exp 1) := by
      have : Real.exp (-1 / 2) = (Real.exp (1 / 2))⁻¹ := by
        rw [← Real.exp_neg]; congr 1; ring
      rw [this, Real.exp_half]; simp
    rw [h1, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3)]
    have : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    have : 0 < Real.sqrt (Real.exp 1) := Real.sqrt_pos.mpr (Real.exp_pos 1)
    field_simp
  rw [hlim] at hprod
  refine hprod.congr (fun D => ?_)
  ring
