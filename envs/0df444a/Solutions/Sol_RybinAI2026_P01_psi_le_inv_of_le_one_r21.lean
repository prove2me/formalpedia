-- Prove2me | solution 1 for RybinAI2026.P01.psi_le_inv_of_le_one_r21
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-03T10:16:11.550199+00:00
-- url     : https://prove2.me/submissions/df17d48f-37a9-4aaf-b550-4f3571b3de57

import Mathlib
set_option autoImplicit false
open MeasureTheory
open intervalIntegral

theorem solution (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    (∫ s in (0 : ℝ)..1, (1 + (t - 1) * s ^ 2)⁻¹) ≤ 1 / t := by
  let f : ℝ → ℝ := fun s => (1 + (t - 1) * s ^ 2)⁻¹
  have htm : t - 1 ≤ 0 := by linarith
  have hden_ge : ∀ s ∈ Set.Icc (0 : ℝ) 1, t ≤ 1 + (t - 1) * s ^ 2 := by
    intro s hs
    have hs2 : s ^ 2 ≤ 1 := by nlinarith [hs.1, hs.2]
    have hcmp : t - 1 ≤ (t - 1) * s ^ 2 := by
      simpa using (mul_le_mul_of_nonpos_left hs2 htm)
    linarith
  have hden_pos : ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 < 1 + (t - 1) * s ^ 2 := by
    intro s hs
    have hge := hden_ge s hs
    linarith
  have hf : ∀ s ∈ Set.Icc (0 : ℝ) 1, f s ≤ 1 / t := by
    intro s hs
    have hle := hden_ge s hs
    have : 1 / (1 + (t - 1) * s ^ 2) ≤ 1 / t := one_div_le_one_div_of_le ht0 hle
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
    intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1) hint hintc hf
  have hconst : ∫ s in (0 : ℝ)..1, (1 / t) = 1 / t := by
    simp [intervalIntegral.integral_const, sub_zero, mul_one]
  simpa [hconst, f] using hmono
