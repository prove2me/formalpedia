-- Prove2me | solution 1 for RybinAI2026.P01.psi_lower_inv_ge_one_r21
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-03T10:01:06.975446+00:00
-- url     : https://prove2.me/submissions/8504673f-f082-4213-a188-f3b54b09ea71

import Mathlib
set_option autoImplicit false
open MeasureTheory
open intervalIntegral

theorem solution (t : ℝ) (ht1 : 1 ≤ t) :
    (1 / t) ≤ ∫ s in (0 : ℝ)..1, (1 + (t - 1) * s ^ 2)⁻¹ := by
  let f : ℝ → ℝ := fun s => (1 + (t - 1) * s ^ 2)⁻¹
  have htm : 0 ≤ t - 1 := by linarith
  have hden_pos : ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 < 1 + (t - 1) * s ^ 2 := by
    intro s hs
    have : 0 ≤ (t - 1) * s ^ 2 := mul_nonneg htm (sq_nonneg s)
    linarith
  have hden_le : ∀ s ∈ Set.Icc (0 : ℝ) 1, 1 + (t - 1) * s ^ 2 ≤ t := by
    intro s hs
    have hs2 : s ^ 2 ≤ 1 := by nlinarith [hs.1, hs.2]
    have hcmp : (t - 1) * s ^ 2 ≤ t - 1 := by
      simpa using (mul_le_mul_of_nonneg_left hs2 htm)
    linarith
  have hf : ∀ s ∈ Set.Icc (0 : ℝ) 1, (1 / t) ≤ f s := by
    intro s hs
    have hp := hden_pos s hs
    have hle := hden_le s hs
    have : 1 / t ≤ 1 / (1 + (t - 1) * s ^ 2) := one_div_le_one_div_of_le hp hle
    simpa [f] using this
  have hcont : ContinuousOn f (Set.uIcc (0 : ℝ) 1) := by
    refine ContinuousOn.inv₀ ?_ ?_
    · fun_prop
    · intro s hs
      exact (hden_pos s (by simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs)).ne'
  have hint : IntervalIntegrable f volume 0 1 := hcont.intervalIntegrable
  have hintc : IntervalIntegrable (fun _ : ℝ => (1 / t)) volume 0 1 :=
    continuous_const.intervalIntegrable _ _
  have hmono :=
    intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1) hintc hint hf
  have hconst : ∫ s in (0 : ℝ)..1, (1 / t) = 1 / t := by
    simp [intervalIntegral.integral_const, sub_zero, mul_one]
  simpa [hconst, f] using hmono
