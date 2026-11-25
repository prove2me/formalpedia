-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_hasFDerivAt_eval_pointOf_5ff81200400e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:49:42.952366+00:00
-- url     : https://prove2.me/submissions/ff1211ea-869d-417b-a5c6-c085c6aa91cf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSmoothLocalGraph
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPolyLocalGenerators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsHolomorphicImplicitGraph
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLocalMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeSmoothLocalGraph
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_hasFDerivAt_eval_mvPolynomial_f7654b357cd2

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
theorem _root_.solution (h : HermNorm n) (q : MvPolynomial (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n)) :
    HasFDerivAt (fun w => eval (h.pointOf w) q)
      ((∑ j, eval (h.pointOf z) (pderiv j q) • ContinuousLinearMap.proj j : (Fin n → ℂ) →L[ℂ] ℂ).comp
        h.pointOfC) z :=
  (hasFDerivAt_eval_mvPolynomial q (h.pointOfC z)).comp z h.pointOfC.hasFDerivAt
end GroundTheory.Heights₂.Heights
