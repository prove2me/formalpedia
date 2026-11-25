-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVariety_retr_rename_761b76ddf8af
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:39:46.510544+00:00
-- url     : https://prove2.me/submissions/bad2df42-161c-465a-a42b-7c7168fc84b7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsJoinVariety
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PJoinVariety

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx liftVar)
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.JoinVariety
variable {K : Type} {ι : K → Type}
namespace GroundTheory.Heights₂.Heights.NumbersDVR.JoinVariety
theorem _root_.solution (F : Type) [Field F] (p : MvPolynomial (Σ k, ι k) F) :
    retr F (rename (liftVar (ι := ι) ptIdx) p) = p := by
  have : (retr F).comp (rename (liftVar (ι := ι) ptIdx)) = AlgHom.id F _ := by
    ext ⟨k, i⟩
    simp [retr, liftVar]
  exact congrArg (fun φ => φ p) this
end GroundTheory.Heights₂.Heights.NumbersDVR.JoinVariety
