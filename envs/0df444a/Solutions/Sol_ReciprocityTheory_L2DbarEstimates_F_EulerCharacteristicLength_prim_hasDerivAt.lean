-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.EulerCharacteristicLength.prim_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:34:10.733921+00:00
-- url     : https://prove2.me/submissions/0aaafbca-6515-4abb-934a-f8e560333187

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_PrimZeroOfNonpos

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
open ReciprocityTheory.L2DbarEstimates.F.EulerCharacteristicLength
namespace ReciprocityTheory.L2DbarEstimates.F.EulerCharacteristicLength
theorem _root_.solution {f : ℝ → ℝ} (hf : Continuous f) (t : ℝ) :
    HasDerivAt (prim f) (f t) t :=
  intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable _ _)
    hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
end ReciprocityTheory.L2DbarEstimates.F.EulerCharacteristicLength
