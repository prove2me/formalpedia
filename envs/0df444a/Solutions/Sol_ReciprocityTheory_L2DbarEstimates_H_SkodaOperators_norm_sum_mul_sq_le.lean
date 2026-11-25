-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.H.SkodaOperators.norm_sum_mul_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:17:14.774373+00:00
-- url     : https://prove2.me/submissions/6adf1f90-439b-4323-b95e-ee14c609ee03

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_WeightedIntegralEqLintegral
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_IntegrableSliceProdFin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.H ReciprocityTheory.L2DbarEstimates.H.SkodaOperators
open MeasureTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.H
open scoped ENNReal InnerProductSpace
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.H.SkodaOperators
theorem _root_.solution {p : ℕ} (g a : Fin p → ℂ) :
    ‖∑ i, g i * a i‖ ^ 2 ≤ vsq g * ∑ i, ‖a i‖ ^ 2 := by
  unfold vsq
  have h1 : ‖∑ i, g i * a i‖ ≤ ∑ i, ‖g i‖ * ‖a i‖ :=
    (norm_sum_le _ _).trans (by simp only [norm_mul]; exact le_rfl)
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖g i‖) (fun i => ‖a i‖)
  calc ‖∑ i, g i * a i‖ ^ 2 ≤ (∑ i, ‖g i‖ * ‖a i‖) ^ 2 := by gcongr
    _ ≤ _ := h2
end ReciprocityTheory.L2DbarEstimates.H.SkodaOperators
