-- Prove2me | solution 1 for UnderstandingML.lda_log_likelihood_ratio
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T10:56:30.072991+00:00
-- url     : https://prove2.me/submissions/204317b2-93c3-444c-b10b-ff9f503fe1a5

import Mathlib
import Definitions.Def_UnderstandingML_Generative

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

open MeasureTheory ProbabilityTheory UnderstandingML in
theorem solution {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.IsSymm)
    (μ₀ μ₁ x : Fin d → ℝ) :
    1 / 2 * dotProduct (x - μ₀) (M.mulVec (x - μ₀)) - 1 / 2 * dotProduct (x - μ₁) (M.mulVec (x - μ₁)) =
      dotProduct (M.mulVec (μ₁ - μ₀)) x +
        1 / 2 * (dotProduct μ₀ (M.mulVec μ₀) - dotProduct μ₁ (M.mulVec μ₁)) := by
  have hs : ∀ a b : Fin d → ℝ, dotProduct a (M.mulVec b) = dotProduct b (M.mulVec a) := by
    intro a b
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hM.eq, dotProduct_comm]
  have e0 := hs μ₀ x
  have e1 := hs μ₁ x
  rw [dotProduct_comm (M.mulVec (μ₁ - μ₀)) x]
  simp only [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct]
  rw [e0, e1]
  ring
