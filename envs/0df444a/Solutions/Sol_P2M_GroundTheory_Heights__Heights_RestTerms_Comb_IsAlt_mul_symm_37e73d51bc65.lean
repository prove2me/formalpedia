-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Comb_IsAlt_mul_symm_37e73d51bc65
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:50:05.167256+00:00
-- url     : https://prove2.me/submissions/7be5cacb-690a-4b56-8230-76f0557d6dfb

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
theorem _root_.solution {P S : MvPolynomial (Fin m) ℚ} (hP : IsAlt P) (hS : S.IsSymmetric) :
    IsAlt (P * S) := by
  intro σ
  rw [map_mul, hP σ, hS σ, smul_mul_assoc]
end IsAlt
end GroundTheory.Heights₂.Heights.RestTerms.Comb
