-- Prove2me | solution 1 for TightCoreset2027.Euclidean.moment_interpolation
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T09:18:17.420116+00:00
-- url     : https://prove2.me/submissions/dbcb61fd-d7fe-459c-a438-66f1cf5fcb26

import Mathlib
open MeasureTheory
set_option autoImplicit false
namespace TightCoreset2027.Euclidean

theorem moment_interpolation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ)
    (hY : Measurable Y)
    (hfour : Integrable (fun ω => |Y ω| ^ 4) μ)
    (hpos : 0 < ∫ ω, |Y ω| ^ 4 ∂μ) :
    (Real.rpow (∫ ω, |Y ω| ^ 2 ∂μ) ((3 : ℝ) / 2)) /
        Real.sqrt (∫ ω, |Y ω| ^ 4 ∂μ) ≤ ∫ ω, |Y ω| ∂μ := by
  have hint : ∀ k : ℕ, k ≤ 4 → Integrable (fun ω => |Y ω| ^ k) μ := by
    intro k hk
    refine Integrable.mono' ((integrable_const 1).add hfour) ?_ ?_
    · exact ((hY.abs).pow_const k).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun ω => ?_
      simp only [Real.norm_eq_abs, abs_pow, abs_abs]
      show |Y ω| ^ k ≤ 1 + |Y ω| ^ 4
      rcases le_total (|Y ω|) 1 with h | h
      · have : |Y ω| ^ k ≤ 1 := pow_le_one₀ (abs_nonneg _) h
        have : 0 ≤ |Y ω| ^ 4 := by positivity
        linarith
      · have : |Y ω| ^ k ≤ |Y ω| ^ 4 := pow_le_pow_right₀ h hk
        linarith
  have h1 := hint 1 (by norm_num)
  have h2 := hint 2 (by norm_num)
  have h3 := hint 3 (by norm_num)
  set A := ∫ ω, |Y ω| ∂μ with hA
  set B := ∫ ω, |Y ω| ^ 2 ∂μ with hB
  set C := ∫ ω, |Y ω| ^ 3 ∂μ with hC
  set D := ∫ ω, |Y ω| ^ 4 ∂μ with hD
  simp only [pow_one] at h1
  have hA0 : 0 ≤ A := integral_nonneg fun ω => abs_nonneg _
  have hB0 : 0 ≤ B := integral_nonneg fun ω => by positivity
  -- quadratic forms
  have q1 : ∀ s : ℝ, 0 ≤ A * (s * s) + (-2 * B) * s + C := by
    intro s
    have : ∫ ω, (s * s * |Y ω| - 2 * s * |Y ω| ^ 2 + |Y ω| ^ 3) ∂μ
        = A * (s * s) + (-2 * B) * s + C := by
      have i1 : Integrable (fun ω => s * s * |Y ω|) μ := h1.const_mul (s * s)
      have i2 : Integrable (fun ω => 2 * s * |Y ω| ^ 2) μ := h2.const_mul (2 * s)
      have i12 : Integrable (fun ω => s * s * |Y ω| - 2 * s * |Y ω| ^ 2) μ := i1.sub i2
      rw [integral_add i12 h3, integral_sub i1 i2, integral_const_mul, integral_const_mul]
      ring
    rw [← this]
    refine integral_nonneg fun ω => ?_
    have : s * s * |Y ω| - 2 * s * |Y ω| ^ 2 + |Y ω| ^ 3 = (s - |Y ω|) ^ 2 * |Y ω| := by ring
    rw [this]; positivity
  have q2 : ∀ s : ℝ, 0 ≤ B * (s * s) + (-2 * C) * s + D := by
    intro s
    have : ∫ ω, (s * s * |Y ω| ^ 2 - 2 * s * |Y ω| ^ 3 + |Y ω| ^ 4) ∂μ
        = B * (s * s) + (-2 * C) * s + D := by
      have i1 : Integrable (fun ω => s * s * |Y ω| ^ 2) μ := h2.const_mul (s * s)
      have i2 : Integrable (fun ω => 2 * s * |Y ω| ^ 3) μ := h3.const_mul (2 * s)
      have i12 : Integrable (fun ω => s * s * |Y ω| ^ 2 - 2 * s * |Y ω| ^ 3) μ := i1.sub i2
      rw [integral_add i12 hfour, integral_sub i1 i2, integral_const_mul, integral_const_mul]
      ring
    rw [← this]
    refine integral_nonneg fun ω => ?_
    have : s * s * |Y ω| ^ 2 - 2 * s * |Y ω| ^ 3 + |Y ω| ^ 4 = (s - |Y ω|) ^ 2 * |Y ω| ^ 2 := by ring
    rw [this]; positivity
  have d1 := discrim_le_zero q1
  have d2 := discrim_le_zero q2
  unfold discrim at d1 d2
  have hBC : B ^ 2 ≤ A * C := by nlinarith
  have hCD : C ^ 2 ≤ B * D := by nlinarith
  have key : B ^ 3 ≤ A ^ 2 * D := by
    rcases eq_or_lt_of_le hB0 with h | h
    · rw [← h]; have : 0 ≤ A ^ 2 * D := by positivity
      simpa using this
    · have h4 : B ^ 4 ≤ A ^ 2 * (B * D) := by
        calc B ^ 4 = (B ^ 2) ^ 2 := by ring
          _ ≤ (A * C) ^ 2 := pow_le_pow_left₀ (by positivity) hBC 2
          _ = A ^ 2 * C ^ 2 := by ring
          _ ≤ A ^ 2 * (B * D) := mul_le_mul_of_nonneg_left hCD (by positivity)
      have : B * B ^ 3 ≤ B * (A ^ 2 * D) := by nlinarith
      exact le_of_mul_le_mul_left this h
  have hsqrtD : 0 < Real.sqrt D := Real.sqrt_pos.2 hpos
  rw [div_le_iff₀ hsqrtD]
  have e1 : Real.rpow B ((3 : ℝ) / 2) = Real.sqrt (B ^ 3) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hB0]
    norm_num
  rw [e1]
  have e2 : A * Real.sqrt D = Real.sqrt (A ^ 2 * D) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hA0]
  rw [e2]
  exact Real.sqrt_le_sqrt key

end TightCoreset2027.Euclidean

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ)
    (hY : Measurable Y)
    (hfour : Integrable (fun ω => |Y ω| ^ 4) μ)
    (hpos : 0 < ∫ ω, |Y ω| ^ 4 ∂μ) :
    (Real.rpow (∫ ω, |Y ω| ^ 2 ∂μ) ((3 : ℝ) / 2)) /
        Real.sqrt (∫ ω, |Y ω| ^ 4 ∂μ) ≤ ∫ ω, |Y ω| ∂μ :=
  TightCoreset2027.Euclidean.moment_interpolation μ Y hY hfour hpos
