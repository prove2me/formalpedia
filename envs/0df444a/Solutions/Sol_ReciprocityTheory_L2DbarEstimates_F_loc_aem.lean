-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.loc_aem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:43:48.327739+00:00
-- url     : https://prove2.me/submissions/67e0946a-9479-4bb2-95eb-34a3f6bba9b4

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_LocalizeA
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
theorem _root_.solution {M E : Type*} [MeasurableSpace M] [NormedAddCommGroup E] (μ : Measure M)
    (a : M → E) (h : AEStronglyMeasurable a μ) :
    AEMeasurable (fun x => ENNReal.ofReal (‖a x‖ ^ 2 * Real.exp (-(fun _ : M => (0 : ℝ)) x))) μ := by
  simp only [neg_zero, Real.exp_zero, mul_one]
  exact ((continuous_norm.pow 2).comp_aestronglyMeasurable h).aemeasurable.ennreal_ofReal
end ReciprocityTheory.L2DbarEstimates.F
