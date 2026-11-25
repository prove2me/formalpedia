-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FrameImplicitGraph_polyDeriv_apply_12bd4a73affc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:34.06256+00:00
-- url     : https://prove2.me/submissions/9a52f602-6393-44e8-a202-31485f676be9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StFrameImplicitGraph
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_HasStrictFDerivAtEval
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PFrameImplicitGraph

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
noncomputable section
open MvPolynomial
open GroundTheory.Heights₂.Heights.FrameImplicitGraph
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.FrameImplicitGraph
theorem _root_.solution (p : MvPolynomial (Fin n) ℂ) (x v : EuclideanSpace ℂ (Fin n)) :
    polyDeriv p x v = ∑ l, eval (fun i => x i) (pderiv l p) * v l := by
  simp [polyDeriv]
end GroundTheory.Heights₂.Heights.FrameImplicitGraph
