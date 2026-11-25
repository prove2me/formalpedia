-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_map_comap_renameEquiv_e95699d65930
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:55:41.337364+00:00
-- url     : https://prove2.me/submissions/7a1f0732-cf09-4af1-a5db-da242dbb1c3f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsRename
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_IntNumRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameHilbFn

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
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution {F : Type u} [Field F] {S K' : Type} {κ : S → Type}
    {ι' : K' → Type} (σ : (Σ s, κ s) ≃ (Σ k', ι' k')) (P : Ideal (MRing ι' F)) :
    (P.comap (rename σ)).map (renameEquiv F σ) = P := by
  have h : P.comap (rename σ) = P.comap (renameEquiv F σ) := rfl
  rw [h]
  exact Ideal.map_comap_of_surjective _ (renameEquiv F σ).surjective P
end GroundTheory.Heights₂.Heights.FieldNumbers
