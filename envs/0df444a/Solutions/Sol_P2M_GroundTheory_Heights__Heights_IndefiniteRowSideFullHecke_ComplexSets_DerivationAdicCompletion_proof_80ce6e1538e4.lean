-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_DerivationAdicCompletion_proof_80ce6e1538e4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:57:15.700055+00:00
-- url     : https://prove2.me/submissions/52e5ef36-0c33-43a9-8e22-a610211ca1c2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDerivationAdicCompletion
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DerivationMemPowOfMemPowSucc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PDerivationAdicCompletion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open AdicCompletion
variable {R : Type} [CommRing R] (I : Ideal R) (D : Derivation ℤ R R)
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace DerivationAdicCompletion
theorem _root_.solution : DerivationAdicCompletion.Statement := by
  intro R _ I D
  refine ⟨derivCompletion I D, fun r => AdicCompletion.ext fun n => ?_⟩
  rfl
end DerivationAdicCompletion
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
