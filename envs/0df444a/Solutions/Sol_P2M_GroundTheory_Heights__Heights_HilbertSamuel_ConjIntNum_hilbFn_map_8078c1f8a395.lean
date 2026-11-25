-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConjIntNum_hilbFn_map_8078c1f8a395
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:29:00.809487+00:00
-- url     : https://prove2.me/submissions/44fdc0fa-c8ca-45d2-ad5a-49eec97c8254

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsConjIntNum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PConjIntNum
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConjIntNum_finrank_gradedPiece_f3564c8558b5

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial NumbersDVR
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.ConjIntNum
variable {K : Type} [DecidableEq K] {ι : K → Type} {F : Type} [Field F]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.ConjIntNum
theorem _root_.solution (τ : F ≃+* F) (J : Ideal (MRing ι F)) :
    hilbFn (J.map (MvPolynomial.map (τ : F →+* F))) = hilbFn J := by
  funext m
  unfold hilbFn
  split_ifs
  · rw [finrank_gradedPiece]
  · rfl
end GroundTheory.Heights₂.Heights.HilbertSamuel.ConjIntNum
