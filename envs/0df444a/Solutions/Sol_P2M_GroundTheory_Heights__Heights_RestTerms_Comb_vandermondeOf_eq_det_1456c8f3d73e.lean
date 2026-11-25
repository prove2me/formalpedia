-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Comb_vandermondeOf_eq_det_1456c8f3d73e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:20:50.741164+00:00
-- url     : https://prove2.me/submissions/956189c4-0828-4ff1-afad-24bc13922e4a

import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qm12_vandermondeOf_eq_det__26efa66ef99e
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
theorem _root_.solution {R : Type*} [CommRing R] (v : Fin m → R) :
    vandermondeOf v = (Matrix.of fun i j : Fin m => v i ^ (m - 1 - (j : ℕ))).det :=
  _root_.P2M_UpperTheory_Reformulated_B_Qm12_vandermondeOf_eq_det__26efa66ef99e v
end GroundTheory.Heights₂.Heights.RestTerms.Comb
