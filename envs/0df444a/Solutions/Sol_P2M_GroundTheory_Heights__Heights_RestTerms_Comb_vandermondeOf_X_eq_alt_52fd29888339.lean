-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Comb_vandermondeOf_X_eq_alt_52fd29888339
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:34:01.201296+00:00
-- url     : https://prove2.me/submissions/6278f558-0332-417d-ba92-1c8022fd7379

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_VandermondeOfEqDet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_AltCoeff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_vandermondeOf_eq_det_1456c8f3d73e

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
theorem _root_.solution :
    vandermondeOf (fun i : Fin m => (X i : MvPolynomial (Fin m) ℚ)) = alt (stair m) := by
  rw [vandermondeOf_eq_det]; rfl
end GroundTheory.Heights₂.Heights.RestTerms.Comb
