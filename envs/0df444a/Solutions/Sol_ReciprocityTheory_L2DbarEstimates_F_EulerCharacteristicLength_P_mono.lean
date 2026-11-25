-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.EulerCharacteristicLength.P_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:02:12.345801+00:00
-- url     : https://prove2.me/submissions/492605f8-761b-4022-9ffb-22c7b51a8ae3

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_PrimZeroOfNonpos
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_EulerCharacteristicLength_primitive_hasDerivAt

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
theorem _root_.solution : Monotone P :=
  monotone_of_deriv_nonneg (fun t => (primitive_hasDerivAt t).differentiableAt)
    (fun t => by rw [(primitive_hasDerivAt t).deriv]; exact expNegInvGlue.nonneg t)
end ReciprocityTheory.L2DbarEstimates.F.EulerCharacteristicLength
