-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_SchSchurEvalMatrix_proof_91c9d5e6207d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:53:59.513001+00:00
-- url     : https://prove2.me/submissions/8210bf34-3541-46c5-bf04-44927230dcb8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchSchurEvalMatrix
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_SchSchurEvalMatrix_aeval_completeSymmetric_753585198774

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
namespace SchSchurEvalMatrix
theorem _root_.solution (h1 : SchCompleteAtRootsOfUnity.Statement) :
    SchSchurEvalMatrix.Statement := by
  intro N k r nu hk hkN
  unfold schur
  rw [AlgHom.map_det]
  congr 1
  ext i j
  rw [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
    SchSchurEvalMatrix.aeval_completeSymmetric h1 N k hk hkN]
  rfl
end SchSchurEvalMatrix
end GroundTheory.Heights₂.Heights.RestTerms
