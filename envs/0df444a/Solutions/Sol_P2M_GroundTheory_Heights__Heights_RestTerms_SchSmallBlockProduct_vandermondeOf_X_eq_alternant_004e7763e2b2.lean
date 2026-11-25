-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_SchSmallBlockProduct_vandermondeOf_X_eq_alternant_004e7763e2b2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:52:57.504805+00:00
-- url     : https://prove2.me/submissions/ec49fff1-78d1-424f-963d-eed5a9a43b7a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_JacobiTrudi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchSmallBlockProduct
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Schur_det_pow_staircase_eq_vandermondeOf_202c942a4a9b


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
theorem _root_.solution (m : ℕ) :
    vandermondeOf (fun i : Fin m => (X i : MvPolynomial (Fin m) ℚ)) =
      alternant (fun j : Fin m => m - 1 - (j : ℕ)) := by
  rw [← Schur.det_pow_staircase_eq_vandermondeOf, alternant, ← Matrix.det_transpose]
  rfl
end SchSmallBlockProduct
end GroundTheory.Heights₂.Heights.RestTerms
