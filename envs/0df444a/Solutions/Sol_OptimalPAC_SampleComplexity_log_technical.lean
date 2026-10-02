-- Prove2me | solution 1 for OptimalPAC.SampleComplexity.log_technical
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T16:07:01.909366+00:00
-- url     : https://prove2.me/submissions/ac2e9ea8-1a98-4c13-bec5-f5a30f330728

import Mathlib

theorem solution (a b c₁ c₂ : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc₁ : 1 ≤ c₁) (hc₂ : 0 ≤ c₂) :
    a * Real.log (c₁ * (c₂ + b / a)) ≤
      a * Real.log (c₁ * (c₂ + Real.exp 1)) + 1 / Real.exp 1 * b := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hc0 : 0 < c₁ := by linarith
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hx : 0 < b / a := div_pos hb0 ha0
  have hu : 0 < c₂ + b / a := by linarith
  have hv : 0 < c₂ + Real.exp 1 := by linarith
  have key : Real.log (c₂ + b / a) - Real.log (c₂ + Real.exp 1) ≤ (b / a) / Real.exp 1 := by
    rw [← Real.log_div hu.ne' hv.ne']
    have h1 := Real.log_le_sub_one_of_pos (div_pos hu hv)
    have h2 : (c₂ + b / a) / (c₂ + Real.exp 1) - 1 = (b / a - Real.exp 1) / (c₂ + Real.exp 1) := by
      field_simp
      ring
    have h3 : (b / a - Real.exp 1) / (c₂ + Real.exp 1) ≤ (b / a) / Real.exp 1 := by
      rw [div_le_div_iff₀ hv he]
      nlinarith [mul_nonneg hx.le hc₂, sq_nonneg (Real.exp 1)]
    linarith
  rw [Real.log_mul hc0.ne' hu.ne', Real.log_mul hc0.ne' hv.ne']
  have h4 : a * ((b / a) / Real.exp 1) = 1 / Real.exp 1 * b := by
    field_simp
  have h5 : a * (Real.log (c₂ + b / a) - Real.log (c₂ + Real.exp 1)) ≤ a * ((b / a) / Real.exp 1) :=
    mul_le_mul_of_nonneg_left key ha0.le
  nlinarith [h4, h5]

