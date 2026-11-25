-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_fderiv_eval_pointOf_apply_eac24c7ed357
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:58:33.258176+00:00
-- url     : https://prove2.me/submissions/cdf0f554-6ae6-4c26-a6a9-c86ec24c1858

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSmoothLocalGraph
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPolyLocalGenerators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsHolomorphicImplicitGraph
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLocalMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeSmoothLocalGraph
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermNorm_pointOfC_apply_7f38c2b360f6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_hasFDerivAt_eval_pointOf_5ff81200400e

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
    (z v : EuclideanSpace ℂ (Fin n)) :
    fderiv ℂ (fun w => eval (h.pointOf w) q) z v =
      ∑ j, eval (h.pointOf z) (pderiv j q) * h.pointOf v j := by
  rw [(hasFDerivAt_eval_pointOf h q z).fderiv]
  simp [HermNorm.pointOfC_apply]
end GroundTheory.Heights₂.Heights
