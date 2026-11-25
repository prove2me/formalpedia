-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.cut_aem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:29:19.265479+00:00
-- url     : https://prove2.me/submissions/d5c59104-a0de-41ec-84bf-7f4338dd1f4e

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_CutoffA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul


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
theorem _root_.solution {M E : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [NormedAddCommGroup E] (μ : Measure M) (u : M → E)
    (hu : AEStronglyMeasurable u μ) (ph : M → ℝ) (hph : Continuous ph) :
    AEMeasurable (fun x => ENNReal.ofReal (‖u x‖ ^ 2 * Real.exp (-ph x))) μ := by
  have h1 : AEMeasurable (fun x => ‖u x‖) μ := hu.norm.aemeasurable
  have h2 : Measurable (fun x => Real.exp (-ph x)) := (Real.continuous_exp.comp hph.neg).measurable
  exact ENNReal.measurable_ofReal.comp_aemeasurable ((h1.pow_const 2).mul h2.aemeasurable)
end ReciprocityTheory.L2DbarEstimates.F
