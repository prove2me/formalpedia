-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.H.SkodaOperators.pt_G
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:55:08.8898+00:00
-- url     : https://prove2.me/submissions/3ff0e3e5-7bc7-4cd0-9339-9b395015e7b0

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_WeightedIntegralEqLintegral
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_IntegrableSliceProdFin
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_SkodaOperators_norm_sum_mul_sq_le

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
theorem _root_.solution {p : ℕ} (g a : Fin p → ℂ) (c : ℝ) (hN : 0 < vsq g) :
    ‖∑ i, g i * a i‖ ^ 2 * Real.exp (-(c + Real.log (vsq g))) ≤
      ∑ i, ‖a i‖ ^ 2 * Real.exp (-c) := by
  have hexp : Real.exp (-(c + Real.log (vsq g))) = Real.exp (-c) / vsq g := by
    rw [neg_add, Real.exp_add, Real.exp_neg (Real.log _), Real.exp_log hN, div_eq_mul_inv]
  rw [hexp, ← Finset.sum_mul]
  have hcs := norm_sum_mul_sq_le g a
  have h1 : ‖∑ i, g i * a i‖ ^ 2 / vsq g ≤ ∑ i, ‖a i‖ ^ 2 := by
    rw [div_le_iff₀ hN, mul_comm]
    exact hcs
  have he := Real.exp_pos (-c)
  calc ‖∑ i, g i * a i‖ ^ 2 * (Real.exp (-c) / vsq g)
      = (‖∑ i, g i * a i‖ ^ 2 / vsq g) * Real.exp (-c) := by ring
    _ ≤ (∑ i, ‖a i‖ ^ 2) * Real.exp (-c) := by gcongr
end ReciprocityTheory.L2DbarEstimates.H.SkodaOperators
