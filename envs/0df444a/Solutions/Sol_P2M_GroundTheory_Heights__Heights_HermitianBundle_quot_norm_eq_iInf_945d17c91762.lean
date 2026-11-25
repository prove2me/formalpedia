-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HermitianBundle_quot_norm_eq_iInf_945d17c91762
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:06:00.2328+00:00
-- url     : https://prove2.me/submissions/12464336-e244-427a-a318-b1ae353ca861

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsBundles
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianBundle_quot_norm_eq_1e4d7c6c0226

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open GroundTheory.Heights₂.Heights.HermitianBundle
variable (M : HermitianBundle K) (F : Submodule (𝓞 K) M.carrier) (hF : M.Saturated F)
namespace GroundTheory.Heights₂.Heights.HermitianBundle
theorem _root_.solution (σ : K →+* ℂ) (ξ : Fibre σ (M.carrier ⧸ F)) :
    ‖FibreSpace.equiv (M.quot F hF).metric σ ξ‖ =
      ⨅ x : {x : Fibre σ M.carrier // F.mkQ.lTensor (ComplexAt σ) x = ξ},
        ‖FibreSpace.equiv M.metric σ x.1‖ := by
  have := quot_projective hF
  rw [quot_norm_eq]
  set V := subFibre M.metric σ F
  set x₀ : FibreSpace M.metric σ :=
    FibreSpace.equiv M.metric σ (fibreMap σ (quotSection M F hF) ξ) with hx₀
  have hq : quotFibreMap M F hF σ ξ = x₀ - V.starProjection x₀ := by
    change Vᗮ.starProjection x₀ = _
    rw [Submodule.starProjection_orthogonal']
    rfl
  rw [hq, Submodule.starProjection_minimal]
  have hlift : F.mkQ.lTensor (ComplexAt σ) ((FibreSpace.equiv M.metric σ).symm x₀) = ξ := by
    change fibreMap σ F.mkQ (fibreMap σ _ ξ) = ξ
    rw [fibreMap_fibreMap, mkQ_comp_quotSection]
    simp [fibreMap]
  have hex := lTensor_exact (ComplexAt σ) (LinearMap.exact_subtype_mkQ F) F.mkQ_surjective
  have hV : ∀ w : FibreSpace M.metric σ, w ∈ V ↔
      F.mkQ.lTensor (ComplexAt σ) ((FibreSpace.equiv M.metric σ).symm w) = 0 := by
    intro w
    rw [hex]
    rfl
  let e : V ≃ {x : Fibre σ M.carrier // F.mkQ.lTensor (ComplexAt σ) x = ξ} :=
    { toFun := fun w ↦ ⟨(FibreSpace.equiv M.metric σ).symm (x₀ - w), by
        rw [map_sub, map_sub, hlift, (hV w).mp w.2, sub_zero]⟩
      invFun := fun x ↦ ⟨x₀ - FibreSpace.equiv M.metric σ x.1, by
        rw [hV, map_sub, map_sub, hlift, LinearEquiv.symm_apply_apply, x.2, sub_self]⟩
      left_inv := fun w ↦ by
        apply Subtype.ext
        simp
      right_inv := fun x ↦ by
        apply Subtype.ext
        simp }
  exact Equiv.iInf_congr e fun w ↦ by simp [e]
end GroundTheory.Heights₂.Heights.HermitianBundle
