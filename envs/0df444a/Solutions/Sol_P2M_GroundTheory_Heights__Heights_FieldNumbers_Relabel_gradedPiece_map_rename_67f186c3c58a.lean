-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_Relabel_gradedPiece_map_rename_67f186c3c58a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:00:37.240727+00:00
-- url     : https://prove2.me/submissions/20d0268a-4d88-4dbc-b89e-ae14c27c8c33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_IntNumRelabel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_Relabel_weight_mapDomain_f5b33ab6271c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_gradedPiece_eq_span_bcb2fa78a226
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b



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
    gradedPiece (I.map (renameEquiv F φ)) d =
      (gradedPiece I (d ∘ e)).map
        ((Ideal.quotientEquivAlg I (I.map (renameEquiv F φ)) (renameEquiv F φ) (Ideal.map_coe _ _).symm).toLinearEquiv :
          (MRing ι₁ F ⧸ I) →ₗ[F] MRing ι₂ F ⧸ I.map (renameEquiv F φ)) := by
  rw [gradedPiece_eq_span, gradedPiece_eq_span, Submodule.map_span, Set.image_image]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq, AlgEquiv.toLinearEquiv_toLinearMap,
    AlgEquiv.toLinearMap_apply, Ideal.quotientEquivAlg_mk, renameEquiv_apply, rename_monomial]
  constructor
  · rintro ⟨d₂, hd₂, rfl⟩
    refine ⟨Finsupp.mapDomain φ.symm d₂, ?_, ?_⟩
    · have h := weight_mapDomain e φ hφ (Finsupp.mapDomain φ.symm d₂)
      rw [← Finsupp.mapDomain_comp, Equiv.self_comp_symm, Finsupp.mapDomain_id, hd₂] at h
      funext k
      have := congrFun h (e k)
      simpa using this.symm
    · rw [← Finsupp.mapDomain_comp, Equiv.self_comp_symm, Finsupp.mapDomain_id]
  · rintro ⟨d₁, hd₁, rfl⟩
    refine ⟨Finsupp.mapDomain φ d₁, ?_, rfl⟩
    rw [weight_mapDomain e φ hφ, hd₁]
    funext k
    simp
end GroundTheory.Heights₂.Heights.FieldNumbers.Relabel
