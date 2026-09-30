-- Prove2me | solution 1 for UnderstandingML.log_loss_risk_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T11:13:32.050989+00:00
-- url     : https://prove2.me/submissions/9814449b-c96a-44c9-86b7-5cb59bda0adf

import Mathlib
import Definitions.Def_UnderstandingML_Generative

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

open MeasureTheory ProbabilityTheory UnderstandingML in
theorem solution {Θ X : Type*} [Fintype X] (P : X → ℝ) (hP : IsPMF P)
    (Pθ : Θ → X → ℝ) (θ : Θ) (hpos : ∀ x, 0 < Pθ θ x) :
    ∑ x, P x * logLoss Pθ θ x = relEntropy P (Pθ θ) + entropy P := by
  unfold logLoss relEntropy entropy
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases h : P x = 0
  · simp [h]
  · rw [Real.log_div h (hpos x).ne', one_div, Real.log_inv]
    ring
