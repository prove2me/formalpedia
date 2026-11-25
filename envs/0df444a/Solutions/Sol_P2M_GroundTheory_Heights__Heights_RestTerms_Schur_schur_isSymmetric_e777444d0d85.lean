-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Schur_schur_isSymmetric_e777444d0d85
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:57:06.033086+00:00
-- url     : https://prove2.me/submissions/43f6fbd4-869f-4fdb-a76f-f10e2061aaf3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_JacobiTrudi
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Schur_rename_completeSymmetric_4ab9f77ac719

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
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
namespace GroundTheory.Heights₂.Heights.RestTerms.Schur
theorem _root_.solution {r : ℕ} (lam : Fin r → ℕ) : (schur σ lam).IsSymmetric := by
  intro e
  unfold schur
  rw [AlgHom.map_det]
  congr 1
  apply Matrix.ext
  intro i j
  simp [rename_completeSymmetric]
end GroundTheory.Heights₂.Heights.RestTerms.Schur
