-- Prove2me | solution 1 for RybinAI2026.P01.mixed_geometric_kernel_window_bound_r16
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T10:26:46.808918+00:00
-- url     : https://prove2.me/submissions/63d27642-55c3-481f-bc88-ce803dc92c84

import Mathlib
set_option autoImplicit false

lemma mgkw7d_bounds (b t : ℝ) (hb : 0 < b) :
    ((Real.sqrt (1 + t ^ 4))⁻¹ * 2 * t ^ 2 / (1 + b * t ^ 4) ≤ 2 * t ^ 2) ∧
    ((1 : ℝ) ≤ t -> (Real.sqrt (1 + t ^ 4))⁻¹ * 2 * t ^ 2 / (1 + b * t ^ 4) ≤ 2) := by
  have hd : (1 : ℝ) ≤ 1 + b * t ^ 4 := by
    have : 0 ≤ b * t ^ 4 := by positivity
    linarith
  have hs : 0 < Real.sqrt (1 + t ^ 4) := Real.sqrt_pos.2 (by positivity)
  have hs1 : (1 : ℝ) ≤ Real.sqrt (1 + t ^ 4) := by
    have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + t ^ 4 from le_add_of_nonneg_right (by positivity))
    rwa [Real.sqrt_one] at h
  have hst : t ^ 2 ≤ Real.sqrt (1 + t ^ 4) := by
    have h0 : Real.sqrt ((t ^ 2) ^ 2) = t ^ 2 := Real.sqrt_sq (by positivity)
    rw [← h0]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hnn : 0 ≤ (Real.sqrt (1 + t ^ 4))⁻¹ * 2 * t ^ 2 := by positivity
  have hdiv : (Real.sqrt (1 + t ^ 4))⁻¹ * 2 * t ^ 2 / (1 + b * t ^ 4)
      ≤ (Real.sqrt (1 + t ^ 4))⁻¹ * 2 * t ^ 2 := div_le_self hnn hd
  have hinv : (Real.sqrt (1 + t ^ 4))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hs1
  constructor
  · have : (Real.sqrt (1 + t ^ 4))⁻¹ * 2 * t ^ 2 ≤ 2 * t ^ 2 := by
      have h2 : 0 ≤ 2 * t ^ 2 := by positivity
      calc (Real.sqrt (1 + t ^ 4))⁻¹ * 2 * t ^ 2
          = (Real.sqrt (1 + t ^ 4))⁻¹ * (2 * t ^ 2) := by ring
        _ ≤ 1 * (2 * t ^ 2) := mul_le_mul_of_nonneg_right hinv h2
        _ = 2 * t ^ 2 := by ring
    linarith
  · intro _
    have : (Real.sqrt (1 + t ^ 4))⁻¹ * 2 * t ^ 2 ≤ 2 := by
      have e : (Real.sqrt (1 + t ^ 4))⁻¹ * 2 * t ^ 2 = 2 * (t ^ 2 / Real.sqrt (1 + t ^ 4)) := by
        field_simp
      have h3 : t ^ 2 / Real.sqrt (1 + t ^ 4) ≤ 1 := (div_le_one hs).mpr hst
      rw [e]; linarith
    linarith

open MeasureTheory in
theorem solution (b T : ℝ) (hb : 0 < b) (hT1 : 1 ≤ T) :
    (∫ t in (0 : ℝ)..T, (Real.sqrt (1 + t ^ 4))⁻¹ * 2 * t ^ 2 / (1 + b * t ^ 4)) ≤
      2 / 3 + 2 * (T - 1) := by
  have hf : Continuous (fun t : ℝ => (Real.sqrt (1 + t ^ 4))⁻¹ * 2 * t ^ 2 / (1 + b * t ^ 4)) := by
    have hs : Continuous fun t : ℝ => Real.sqrt (1 + t ^ 4) := by fun_prop
    refine Continuous.div ?_ (by fun_prop) (fun t => by positivity)
    refine Continuous.mul (Continuous.mul ?_ continuous_const) (by fun_prop)
    exact hs.inv₀ (fun t => (Real.sqrt_pos.2 (by positivity)).ne')
  have hA : (∫ t in (0 : ℝ)..1, (Real.sqrt (1 + t ^ 4))⁻¹ * 2 * t ^ 2 / (1 + b * t ^ 4))
      ≤ ∫ t in (0 : ℝ)..1, (2 : ℝ) * t ^ 2 :=
    intervalIntegral.integral_mono_on (by norm_num) (hf.intervalIntegrable _ _)
      ((by fun_prop : Continuous fun t : ℝ => (2 : ℝ) * t ^ 2).intervalIntegrable _ _)
      (fun t _ => (mgkw7d_bounds b t hb).1)
  have hA' : (∫ t in (0 : ℝ)..1, (2 : ℝ) * t ^ 2) = 2 / 3 := by
    rw [intervalIntegral.integral_const_mul, integral_pow]; norm_num
  have hB : (∫ t in (1 : ℝ)..T, (Real.sqrt (1 + t ^ 4))⁻¹ * 2 * t ^ 2 / (1 + b * t ^ 4))
      ≤ ∫ _ in (1 : ℝ)..T, (2 : ℝ) :=
    intervalIntegral.integral_mono_on hT1 (hf.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _)
      (fun t ht => (mgkw7d_bounds b t hb).2 ht.1)
  have hB' : (∫ _ in (1 : ℝ)..T, (2 : ℝ)) = 2 * (T - 1) := by
    rw [intervalIntegral.integral_const]; simp; ring
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1) (hf.intervalIntegrable _ _)
    (hf.intervalIntegrable _ _)]
  linarith
