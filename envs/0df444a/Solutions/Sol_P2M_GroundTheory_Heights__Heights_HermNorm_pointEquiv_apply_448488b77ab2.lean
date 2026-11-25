-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HermNorm_pointEquiv_apply_448488b77ab2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:28:12.780456+00:00
-- url     : https://prove2.me/submissions/5f05e599-4e5d-48ac-b353-ed93dedee20a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeTangentDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeKrullDimLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeTangentAverage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StFrameJacobianGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeTangentDim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Module
open scoped ENNReal
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
namespace HermNorm
theorem _root_.solution (h : HermNorm n) (y : EuclideanSpace ℂ (Fin n)) :
    h.pointEquiv y = h.pointOf y := rfl
end HermNorm
end GroundTheory.Heights₂.Heights
