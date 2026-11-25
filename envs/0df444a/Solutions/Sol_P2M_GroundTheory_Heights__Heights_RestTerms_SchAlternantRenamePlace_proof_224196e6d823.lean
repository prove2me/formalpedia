-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_SchAlternantRenamePlace_proof_224196e6d823
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:54:20.939233+00:00
-- url     : https://prove2.me/submissions/c90737f4-16aa-46ca-bc5a-70f1f32cde13

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchAlternantRenamePlace
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_rename_alternant_equiv_9b419387e508

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
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace SchAlternantRenamePlace
theorem _root_.solution : SchAlternantRenamePlace.Statement := by
  intro r a c v
  have hg : smallBlockPlace r a c =
      (fun p : Fin (r + a) => ((0 : Fin 1), p)) ∘ smallBlockEquiv r a c := by
    funext x
    exact Prod.ext (Subsingleton.elim _ _) rfl
  have hs : (smallBlockEquiv r a c).symm = smallBlockOf r a c := rfl
  rw [hg, ← rename_rename]
  congr 1
  rw [rename_alternant_equiv, hs]
end SchAlternantRenamePlace
end GroundTheory.Heights₂.Heights.RestTerms
