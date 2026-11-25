-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Schur_det_hMatrix_staircase_8f257c117f9e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:53:06.745894+00:00
-- url     : https://prove2.me/submissions/53809e74-cab3-423a-b3ad-030cb9130c11

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_JacobiTrudi
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Schur_completeSymmetric_natSub_050630c5ac60

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms GroundTheory.Heights₂.Heights.RestTerms.Schur
open MvPolynomial Finset
noncomputable section
variable {m : ℕ}
namespace GroundTheory.Heights₂.Heights.RestTerms.Schur
theorem _root_.solution :
    (hMatrix (fun i : Fin m => m - 1 - (i : ℕ))).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · apply prod_eq_one
    intro i _
    have := i.isLt
    simp only [hMatrix, Matrix.of_apply, completeSymmetric_natSub]
    rw [if_pos (by omega), show m - 1 - (i : ℕ) - (m - 1 - (i : ℕ)) = 0 by omega, hsymm_zero]
  · intro i c hci
    simp only [hMatrix, Matrix.of_apply, completeSymmetric_natSub]
    rw [if_neg]
    have := c.isLt
    have : (c : ℕ) < i := hci
    omega
end GroundTheory.Heights₂.Heights.RestTerms.Schur
