-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_proof_25d91be13206
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:21:40.414718+00:00
-- url     : https://prove2.me/submissions/3e61e78d-53c8-4e83-9890-23c374ddffd6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsVectorOrbits
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PIsotropicScaling
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_scalingMap_apply_eff752ab2046
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_scalingMap_zero_dc5db613c807
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_scalingMap_comp_dd4b298a92c9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_scalingMap_isometry_7e0d595ba1e1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_sub_one_add_inv_sub_one_add_mul_eq_zero_9968b8cf05bb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_exists_nsmul_mem_b0df14af21b1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_IsotropicScaling_scalingMap_mem_2f9ce7653ab7
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_mem_unitaryGroup
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.conj_conj



set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module
open scoped Pointwise
noncomputable section
open GroundTheory.Heights₂.Heights.FiniteCovolume.IsotropicScaling
variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume.IsotropicScaling
theorem _root_.solution (h : HermitianForm F E W) (h₁ : WittPartner.Statement h) :
    IsotropicScaling.Statement h := by
  intro La x₀ hLa hint hx₀ hne hiso
  obtain ⟨w₀, hvw, hww⟩ := h₁ x₀ hne hiso
  have hwv : h.toSesq w₀ x₀ = 1 := by rw [← h.isSymm.eq x₀ w₀, hvw, map_one]
  obtain ⟨N, hN, hNw⟩ := exists_nsmul_mem hLa w₀
  refine ⟨N, hN, fun ε hε => ?_⟩
  have he : ((ε : 𝓞 E) : E) ≠ 0 := by exact_mod_cast ε.ne_zero
  have hce : conj F E ((ε : 𝓞 E) : E) ≠ 0 := (map_ne_zero _).2 he
  have hinv : (((ε⁻¹ : (𝓞 E)ˣ) : 𝓞 E) : E) = ((ε : 𝓞 E) : E)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by exact_mod_cast ε.inv_mul)
  set e : E := ((ε : 𝓞 E) : E)
  have hcinv : (conj F E e⁻¹)⁻¹ = conj F E e := by rw [map_inv₀, inv_inv]
  have k1 : e - 1 + (e⁻¹ - 1) + (e - 1) * (e⁻¹ - 1) = 0 := sub_one_add_inv_sub_one_add_mul_eq_zero he
  have k2 : (conj F E e)⁻¹ - 1 + (conj F E e - 1) + ((conj F E e)⁻¹ - 1) * (conj F E e - 1) = 0 := by
    have := sub_one_add_inv_sub_one_add_mul_eq_zero (inv_ne_zero hce); rwa [inv_inv] at this
  have k3 : e⁻¹ - 1 + (e - 1) + (e⁻¹ - 1) * (e - 1) = 0 := by
    have := sub_one_add_inv_sub_one_add_mul_eq_zero (inv_ne_zero he); rwa [inv_inv] at this
  have k4 : conj F E e - 1 + ((conj F E e)⁻¹ - 1) + (conj F E e - 1) * ((conj F E e)⁻¹ - 1) = 0 :=
    sub_one_add_inv_sub_one_add_mul_eq_zero hce
  have h1 : scalingMap h x₀ w₀ (e - 1) ((conj F E e)⁻¹ - 1) ∘ₗ
      scalingMap h x₀ w₀ (e⁻¹ - 1) (conj F E e - 1) = LinearMap.id := by
    rw [scalingMap_comp h hiso hww hvw hwv, k1, k2, scalingMap_zero]
  have h2 : scalingMap h x₀ w₀ (e⁻¹ - 1) (conj F E e - 1) ∘ₗ
      scalingMap h x₀ w₀ (e - 1) ((conj F E e)⁻¹ - 1) = LinearMap.id := by
    rw [scalingMap_comp h hiso hww hvw hwv, k3, k4, scalingMap_zero]
  let γ : W ≃ₗ[E] W := LinearEquiv.ofLinearMap _ _ h1 h2
  have hγU : γ ∈ h.unitaryGroup := HermitianForm.mem_unitaryGroup.2 fun x y =>
    scalingMap_isometry h hiso hww hvw hwv
      (by rw [map_sub, map_inv₀, conj_conj, map_one]; exact k1) x y
  have memT : ∀ x ∈ La, scalingMap h x₀ w₀ (e - 1) ((conj F E e)⁻¹ - 1) x ∈ La :=
    fun x hx => scalingMap_mem h hLa hint hx₀ hNw hε hx
  have memT' : ∀ x ∈ La, scalingMap h x₀ w₀ (e⁻¹ - 1) (conj F E e - 1) x ∈ La := fun x hx => by
    have := scalingMap_mem h hLa hint hx₀ hNw (inv_mem hε) hx
    rwa [hinv, hcinv] at this
  refine ⟨⟨γ, hγU⟩, ?_, ?_⟩
  · rw [latticeStab, MulAction.mem_stabilizer_iff]
    ext y
    refine ⟨fun hy => ?_, fun hy => ⟨_, memT' y hy, ?_⟩⟩
    · obtain ⟨x, hx, rfl⟩ := hy
      exact memT x hx
    change scalingMap h x₀ w₀ (e - 1) ((conj F E e)⁻¹ - 1)
      (scalingMap h x₀ w₀ (e⁻¹ - 1) (conj F E e - 1) y) = y
    rw [← LinearMap.comp_apply, h1, LinearMap.id_apply]
  · change scalingMap h x₀ w₀ (e - 1) ((conj F E e)⁻¹ - 1) x₀ = e • x₀
    rw [scalingMap_apply, hwv, hiso]
    module
end GroundTheory.Heights₂.Heights.FiniteCovolume.IsotropicScaling
