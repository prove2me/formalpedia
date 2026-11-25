-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_SchRootOfUnityBialternant_proof_51adc27b3f55
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:18:44.164224+00:00
-- url     : https://prove2.me/submissions/b6056ce8-7b53-4bd6-858a-48eb1608a22d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_JacobiTrudi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchRootOfUnityBialternant
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_aeval_vandermondeOf_X_4558a85fce16
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Schur_det_pow_add_staircase_eq_0e7b2e6105c4


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
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace SchRootOfUnityBialternant
theorem _root_.solution (h1 : SchSchurEvalMatrix.Statement) :
    SchRootOfUnityBialternant.Statement := by
  intro k nu hk
  have hw : ∀ j : Fin k, rootOfUnityPoint k k j = rootOfUnity k ^ (j : ℕ) := fun j => by
    simp [rootOfUnityPoint, j.isLt]
  have key := congrArg (aeval (rootOfUnityPoint k k)) (Schur.det_pow_add_staircase_eq nu)
  rw [map_mul, h1 k k k nu hk le_rfl, AlgHom.map_det, aeval_vandermondeOf_X] at key
  have hv : rootOfUnityPoint k k = fun i : Fin k => rootOfUnity k ^ (i : ℕ) := funext hw
  rw [hv] at key
  rw [← key]
  congr 1
  ext i j
  simp [AlgHom.mapMatrix_apply, Matrix.map_apply, aeval_X, ← pow_mul]
end SchRootOfUnityBialternant
end GroundTheory.Heights₂.Heights.RestTerms
