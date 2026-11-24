-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConormalGenerationGeneric_proof_f41f288e0b9b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:59.009385+00:00
-- url     : https://prove2.me/submissions/04aa9127-7599-4787-9c84-4268446d7a48

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StConormalGenerationGeneric
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_GenericGradient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PConormalGenerationGeneric
import Theorems.Thm_UpperTheory_Reformulated_B_Qf34_proof


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
open MvPolynomial KaehlerDifferential TensorProduct IsLocalRing
namespace GroundTheory.Heights₂.Heights
namespace ConormalGenerationGeneric
theorem _root_.solution : ConormalGenerationGeneric.Statement :=
  _root_.UpperTheory.Reformulated.B.Qf34.proof
end ConormalGenerationGeneric
end GroundTheory.Heights₂.Heights
