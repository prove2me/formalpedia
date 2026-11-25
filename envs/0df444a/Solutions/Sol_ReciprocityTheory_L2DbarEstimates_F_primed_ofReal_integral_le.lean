-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.primed_ofReal_integral_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:28:42.21397+00:00
-- url     : https://prove2.me/submissions/285bb23c-5335-461b-a457-88fdb94010e7

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_Primed
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ)
    (hf : ∀ x, 0 ≤ f x) : ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  by_cases hm : AEStronglyMeasurable f μ
  · rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hf) hm]
    exact ENNReal.ofReal_toReal_le
  · rw [integral_non_aestronglyMeasurable hm]
    simp
end ReciprocityTheory.L2DbarEstimates.F
