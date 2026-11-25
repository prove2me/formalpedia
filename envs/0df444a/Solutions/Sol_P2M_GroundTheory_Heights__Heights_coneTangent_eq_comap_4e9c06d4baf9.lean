-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_coneTangent_eq_comap_4e9c06d4baf9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:26:04.133288+00:00
-- url     : https://prove2.me/submissions/1d13efac-374a-44f6-b2af-9bbd0b7ca8b4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSmoothLocalGraph
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPolyLocalGenerators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsHolomorphicImplicitGraph
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLocalMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeSmoothLocalGraph

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
open MvPolynomial Module
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (z : EuclideanSpace ℂ (Fin n)) :
    coneTangent h J z = (polyTangent (J : Set (MvPolynomial (Fin n) ℂ)) (h.pointOf z)).comap
      (h.pointOfE : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] (Fin n → ℂ)) := rfl
end GroundTheory.Heights₂.Heights
