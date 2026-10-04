-- Prove2me | solution 1 for RybinAI2026.P01.mixed_geometric_kernel_bounds_r16
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T09:03:28.853697+00:00
-- url     : https://prove2.me/submissions/fab08092-efe6-488b-ab9c-80afe69bcc15

import Mathlib
set_option autoImplicit false

open MeasureTheory in
theorem solution (b t : ℝ) (hb : 0 < b) :
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
