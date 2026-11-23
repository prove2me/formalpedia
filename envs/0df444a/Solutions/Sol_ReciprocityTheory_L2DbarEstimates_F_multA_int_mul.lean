-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.multA_int_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:34:19.536275+00:00
-- url     : https://prove2.me/submissions/c31f6d76-5a4a-45cc-93ba-fd85d659ee25

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_IntegrableOnCompactOfLocL2

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
theorem _root_.solution {M : Type*} [TopologicalSpace M] [T2Space M] [MeasurableSpace M]
    [OpensMeasurableSpace M] (μ : Measure M) (u c : M → ℂ)
    (hu : ∀ K, IsCompact K → IntegrableOn u K μ) (hc : Continuous c) (hcs : HasCompactSupport c) :
    Integrable (fun x => u x * c x) μ := by
  have h1 : IntegrableOn (fun x => u x * c x) (tsupport c) μ :=
    (hu _ hcs).mul_continuousOn hc.continuousOn hcs
  exact (integrableOn_iff_integrable_of_support_subset
    ((Function.support_mul_subset_right _ _).trans (subset_tsupport c))).mp h1
end ReciprocityTheory.L2DbarEstimates.F
