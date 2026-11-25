-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_lengthFormulaDimOne_ebd95ca81df3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:04:29.654658+00:00
-- url     : https://prove2.me/submissions/dcf22096-55a8-4a00-9604-4e4f22329eb9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Statements
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthCokerEqKerAddDimOneOrderSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthTwoGeneratorQuotient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Length
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_dimOneFormula


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
universe u v
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution : LengthFormulaDimOne.Statement.{u, v} :=
  ReciprocityTheory.ChartRestriction.G.AI.dimOneFormula
end GroundTheory.Heights₂.Heights.NumbersDVR
