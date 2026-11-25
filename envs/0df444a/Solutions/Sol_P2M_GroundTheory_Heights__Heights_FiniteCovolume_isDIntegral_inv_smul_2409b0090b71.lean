-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_isDIntegral_inv_smul_2409b0090b71
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:19:48.641641+00:00
-- url     : https://prove2.me/submissions/caa8ea81-a5c9-496f-9413-412033b129f3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsAdaptedReduction
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsHyperbolicPairs
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StLineNormalForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StComplementLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PAdaptedReduction
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_sesq_unitary_smul_183a127d023b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_unitary_smul_scalar_smul_5c8918aaa95a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_mem_inv_smul_iff_7dce9a2084b8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_dualLattice_inv_smul_6bc15559e293

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module
open scoped Pointwise
noncomputable section
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]
variable {h : HermitianForm F E W}
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
theorem _root_.solution (g : h.unitaryGroup) {D : ℕ} {La : AddSubgroup W}
    (hLa : IsDIntegral h D La) : IsDIntegral h D (g⁻¹ • La) := by
  set γ : W ≃ₗ[E] W := ((g⁻¹ : h.unitaryGroup) : W ≃ₗ[E] W) with hγ
  have hinj : Function.Injective (DistribMulAction.toAddMonoidEnd (W ≃ₗ[E] W) W γ) :=
    fun x y hxy => γ.injective hxy
  have hrel : (g⁻¹ • La).relIndex (dualLattice h (g⁻¹ • La)) =
      La.relIndex (dualLattice h La) := by
    rw [dualLattice_inv_smul]
    change (γ • La).relIndex (γ • dualLattice h La) = _
    rw [AddSubgroup.pointwise_smul_def, AddSubgroup.pointwise_smul_def]
    exact AddSubgroup.relIndex_map_map_of_injective _ _ hinj
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro a x hx
    rw [mem_inv_smul_iff] at hx ⊢
    rw [unitary_smul_scalar_smul]
    exact hLa.isLattice.smul_mem a _ hx
  · have hfg := hLa.isLattice.fg
    change (γ • La).FG
    rw [AddSubgroup.pointwise_smul_def]
    rw [AddSubgroup.fg_iff_exists_fin_addMonoidHom] at hfg ⊢
    obtain ⟨k, f, hf⟩ := hfg
    exact ⟨k, γ.toLinearMap.toAddMonoidHom.comp f, by
      rw [AddMonoidHom.range_comp, hf]
      rfl⟩
  · have hset : ((g⁻¹ • La : AddSubgroup W) : Set W) =
        γ.toLinearMap '' (La : Set W) := by
      ext y
      constructor
      · intro hy
        exact ⟨g • y, mem_inv_smul_iff.1 hy, inv_smul_smul g y⟩
      · rintro ⟨x, hx, rfl⟩
        change g⁻¹ • x ∈ g⁻¹ • La
        rw [mem_inv_smul_iff, smul_inv_smul]
        exact hx
    rw [hset, Submodule.span_image, hLa.isLattice.span_eq_top, Submodule.map_top,
      LinearMap.range_eq_top]
    exact LinearEquiv.surjective _
  · intro x hx y hy
    rw [mem_inv_smul_iff] at hx hy
    rw [← sesq_unitary_smul g]
    exact hLa.integral _ hx _ hy
  · rw [hrel]
    exact hLa.index_ne_zero
  · rw [hrel]
    exact hLa.index_le
end GroundTheory.Heights₂.Heights.FiniteCovolume
