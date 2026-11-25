-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_SchSmallBlockProduct_vandermondeOf_X_comp_ae80ada4396d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:52:55.68648+00:00
-- url     : https://prove2.me/submissions/c4359bf6-14b3-4a86-8084-d9ae20dc6599

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_JacobiTrudi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchSmallBlockProduct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace SchSmallBlockProduct
theorem _root_.solution {m : ℕ} {κ : Type*} (g : Fin m → κ) :
    vandermondeOf (fun i => (X (g i) : MvPolynomial κ ℚ)) =
      rename g (vandermondeOf (fun i : Fin m => (X i : MvPolynomial (Fin m) ℚ))) := by
  simp [vandermondeOf, map_prod, map_sub, rename_X]
end SchSmallBlockProduct
end GroundTheory.Heights₂.Heights.RestTerms
