-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.chT_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:31:27.270922+00:00
-- url     : https://prove2.me/submissions/b742f150-f42a-4b8e-ae72-ec9334a59559

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_ChartA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_continuous


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set Function
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution {n : ℕ} {M : Type*} [MeasurableSpace M] (μ : Measure M) (G : M → V n)
    (hG : AEStronglyMeasurable G μ) (j : Fin n) : AEStronglyMeasurable (fun x => G x j) μ := (EuclideanSpace.proj (𝕜 := ℂ) j).continuous.comp_aestronglyMeasurable hG
end ReciprocityTheory.L2DbarEstimates.F
