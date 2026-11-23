-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.EulerCharacteristicLength.sig_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:38:27.576795+00:00
-- url     : https://prove2.me/submissions/d37afe95-44fa-481c-81fd-4e96d8c47d76

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_PrimZeroOfNonpos
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_EulerCharacteristicLength_prim_hasDerivAt
import Theorems.Thm_P2M_ReciprocityTheory_L2DbarEstimates_F_EulerCharacteristicLength_primitive_contDiff__2a60c3cf0d38

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
theorem _root_.solution (t : ℝ) : HasDerivAt sig (P t) t := prim_hasDerivAt primitive_contDiff₂.continuous t
end ReciprocityTheory.L2DbarEstimates.F.EulerCharacteristicLength
