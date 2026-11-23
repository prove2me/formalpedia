-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.EulerCharacteristicLength.rho_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:34:11.168724+00:00
-- url     : https://prove2.me/submissions/b54cf08d-53cc-4567-90d4-61db81b062ea

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
theorem _root_.solution : ContDiff ℝ ∞ expNegInvGlue := expNegInvGlue.contDiff
end ReciprocityTheory.L2DbarEstimates.F.EulerCharacteristicLength
