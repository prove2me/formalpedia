-- Prove2me | solution 1 for SuttonBartoRL.Traces.lms_step_fading_form
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T11:40:36.827212+00:00
-- url     : https://prove2.me/submissions/992503f7-bda1-4c8e-bb4f-e9f7cadeb662

import Mathlib
import Definitions.Def_SuttonBartoRL_Traces_DutchMC

set_option autoImplicit false

open Matrix SuttonBartoRL.Traces in
theorem solution {d : ℕ} (α G : ℝ) (x : ℕ → Fin d → ℝ) (w₀ : Fin d → ℝ) (t : ℕ) :
    lmsWeights α G x w₀ (t + 1) =
      fadingMatrix α x t *ᵥ lmsWeights α G x w₀ t + (α * G) • x t := by
  funext i
  simp only [lmsWeights, fadingMatrix, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.add_apply,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.smul_mulVec]
  simp only [Matrix.mulVec, Matrix.vecMulVec, dotProduct, Matrix.of_apply]
  rw [show ∑ j, x t i * x t j * lmsWeights α G x w₀ t j
      = x t i * ∑ j, lmsWeights α G x w₀ t j * x t j by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring]
  ring
