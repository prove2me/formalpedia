-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.twb_wmono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:18:07.352741+00:00
-- url     : https://prove2.me/submissions/d2a75271-4763-4ef0-a72d-fa52de99e475

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_TwBound
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution {α : Type*} [MeasurableSpace α] (μ : Measure α) (f ρ₁ ρ₂ : α → ℝ) (c : ℝ)
    (hc : 0 ≤ c) (hf : ∀ x, 0 ≤ f x) (h : ∀ x, ρ₁ x ≤ c * ρ₂ x) :
    ∫⁻ x, ENNReal.ofReal (f x * ρ₁ x) ∂μ ≤ ENNReal.ofReal c * ∫⁻ x, ENNReal.ofReal (f x * ρ₂ x) ∂μ := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono (fun x => ?_)
  rw [← ENNReal.ofReal_mul hc]
  refine ENNReal.ofReal_le_ofReal ?_
  calc f x * ρ₁ x ≤ f x * (c * ρ₂ x) := mul_le_mul_of_nonneg_left (h x) (hf x)
    _ = c * (f x * ρ₂ x) := by ring
end ReciprocityTheory.L2DbarEstimates.I
