-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Comb_IsAlt_zero_8589bd36c748
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:14:09.448802+00:00
-- url     : https://prove2.me/submissions/a6ddae67-c6f0-42e2-82af-afd23cec9dbf

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
theorem _root_.solution : IsAlt (0 : MvPolynomial (Fin m) ℚ) := by intro σ; simp
end IsAlt
end GroundTheory.Heights₂.Heights.RestTerms.Comb
