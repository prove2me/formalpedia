-- Prove2me | solution 1 for StabGen.Entropy.avgLoss_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T15:09:19.093989+00:00
-- url     : https://prove2.me/submissions/ee2cade5-65f0-491b-bd9d-b5eb329fa8e0

import Mathlib
import Definitions.Def_StabGen_Entropy_Model

open MeasureTheory StabGen.Entropy in
theorem solution {Θ Z : Type*} [MeasurableSpace Θ] (ν : Measure Θ)
    (r : Θ → Z → ℝ) (M : ℝ)
    (hr_meas : ∀ z, Measurable (fun θ => r θ z))
    (hr : ∀ θ z, 0 ≤ r θ z ∧ r θ z ≤ M)
    (g g' : Θ → ℝ) (hg : Integrable g ν) (hg' : Integrable g' ν) (z : Z) :
    |avgLoss ν r g z - avgLoss ν r g' z| ≤ M * ∫ θ, |g θ - g' θ| ∂ν := by
  unfold avgLoss
  have hb : ∀ᵐ θ ∂ν, ‖r θ z‖ ≤ M := Filter.Eventually.of_forall fun θ => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hr θ z).1]; exact (hr θ z).2
  have h1 : Integrable (fun θ => r θ z * g θ) ν :=
    hg.bdd_mul (hr_meas z).aestronglyMeasurable hb
  have h2 : Integrable (fun θ => r θ z * g' θ) ν :=
    hg'.bdd_mul (hr_meas z).aestronglyMeasurable hb
  rw [← integral_sub h1 h2, ← integral_const_mul]
  calc |∫ θ, (r θ z * g θ - r θ z * g' θ) ∂ν|
      ≤ ∫ θ, |r θ z * g θ - r θ z * g' θ| ∂ν := abs_integral_le_integral_abs
    _ ≤ ∫ θ, M * |g θ - g' θ| ∂ν := by
        apply integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall fun θ => abs_nonneg _
        · exact ((hg.sub hg').abs).const_mul M
        · refine Filter.Eventually.of_forall fun θ => ?_
          simp only
          rw [← mul_sub, abs_mul, abs_of_nonneg (hr θ z).1]
          exact mul_le_mul_of_nonneg_right (hr θ z).2 (abs_nonneg _)
