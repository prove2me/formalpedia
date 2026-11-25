-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FrameImplicitGraph_hasStrictFDerivAt_phi_7970470bf85b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:31.616889+00:00
-- url     : https://prove2.me/submissions/89afe733-2c49-4582-a279-352a7f9867bd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StFrameImplicitGraph
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_HasStrictFDerivAtEval
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PFrameImplicitGraph
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FrameImplicitGraph_hasStrictFDerivAt_eval_bed54b8aac66
import Theorems.Thm_UpperTheory_Reformulated_B_Qi29_hasStrictFDerivAt_eval


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
theorem _root_.solution (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) (f : {j // j ∉ I} → MvPolynomial (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n)) :
    HasStrictFDerivAt (phi b I f) (phiDeriv b I f x) x :=
  (projCLM b I).hasStrictFDerivAt.prodMk (hasStrictFDerivAt_pi.2 fun k => hasStrictFDerivAt_eval (f k) x)
end GroundTheory.Heights₂.Heights.FrameImplicitGraph
