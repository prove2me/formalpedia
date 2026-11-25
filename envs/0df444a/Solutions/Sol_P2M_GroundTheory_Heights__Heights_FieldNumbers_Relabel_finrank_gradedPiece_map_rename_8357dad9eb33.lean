-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_Relabel_finrank_gradedPiece_map_rename_8357dad9eb33
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:36:50.775152+00:00
-- url     : https://prove2.me/submissions/992f2624-89d4-4f3a-8a25-c47830c04c56

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_IntNumRelabel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_Relabel_gradedPiece_map_rename_67f186c3c58a

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter
noncomputable section
open GroundTheory.Heights₂.Heights.FieldNumbers.Relabel
variable {K₁ K₂ : Type*} [DecidableEq K₁] [DecidableEq K₂] {ι₁ : K₁ → Type*} {ι₂ : K₂ → Type*}
  (e : K₁ ≃ K₂) (φ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)) (hφ : ∀ v, (φ v).1 = e v.1)
  {F : Type*} [Field F]
include hφ
namespace GroundTheory.Heights₂.Heights.FieldNumbers.Relabel
theorem _root_.solution (I : Ideal (MRing ι₁ F)) (d : K₂ → ℕ) :
    Module.finrank F (gradedPiece (I.map (renameEquiv F φ)) d) =
      Module.finrank F (gradedPiece I (d ∘ e)) := by
  rw [gradedPiece_map_rename e φ hφ, LinearEquiv.finrank_map_eq]
end GroundTheory.Heights₂.Heights.FieldNumbers.Relabel
