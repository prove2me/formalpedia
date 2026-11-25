-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConjIntNum_finrank_gradedPiece_f3564c8558b5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:14:46.545806+00:00
-- url     : https://prove2.me/submissions/52f79af2-10f8-43c4-8e34-cebcfdd6238e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsConjIntNum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PConjIntNum
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConjIntNum_quotEquiv_smul_b0bc8a006225

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
theorem _root_.solution (τ : F ≃+* F) (J : Ideal (MRing ι F)) (m : K → ℕ) :
    Module.finrank F (gradedPiece (J.map (MvPolynomial.map (τ : F →+* F))) m) =
      Module.finrank F (gradedPiece J m) := by
  have h := rank_eq_of_equiv_equiv (τ : F → F) (pieceEquiv τ J m) τ.bijective
    (fun c x => Subtype.ext (quotEquiv_smul τ J c x))
  simp only [Module.finrank, h]
end GroundTheory.Heights₂.Heights.HilbertSamuel.ConjIntNum
