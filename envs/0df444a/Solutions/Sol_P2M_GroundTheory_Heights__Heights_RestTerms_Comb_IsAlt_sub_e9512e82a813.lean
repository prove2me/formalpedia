-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Comb_IsAlt_sub_e9512e82a813
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:14:13.430743+00:00
-- url     : https://prove2.me/submissions/8fd52ddb-c01b-406b-a52e-da052fd40fa6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_VandermondeOfEqDet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_AltCoeff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms GroundTheory.Heights₂.Heights.RestTerms.Comb
open MvPolynomial Finset Equiv
noncomputable section
variable {m : ℕ}
namespace GroundTheory.Heights₂.Heights.RestTerms.Comb
namespace IsAlt
theorem _root_.solution {P Q : MvPolynomial (Fin m) ℚ} (hP : IsAlt P) (hQ : IsAlt Q) : IsAlt (P - Q) := by
  intro σ; rw [map_sub, hP σ, hQ σ, smul_sub]
end IsAlt
end GroundTheory.Heights₂.Heights.RestTerms.Comb
