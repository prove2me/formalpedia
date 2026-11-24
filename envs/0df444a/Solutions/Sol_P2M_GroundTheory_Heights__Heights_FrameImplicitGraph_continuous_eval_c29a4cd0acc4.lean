-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FrameImplicitGraph_continuous_eval_c29a4cd0acc4
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:07.544373+00:00
-- url     : https://prove2.me/submissions/6b0e6002-2f4c-4591-b1e1-46db9a2f6c74

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
theorem _root_.solution (p : MvPolynomial (Fin n) ℂ) :
    Continuous fun y : EuclideanSpace ℂ (Fin n) => eval (fun i => y i) p :=
  continuous_iff_continuousAt.2 fun x => (hasStrictFDerivAt_eval p x).continuousAt
end GroundTheory.Heights₂.Heights.FrameImplicitGraph
