-- Prove2me | solution 1 for ValuationSubring.mem_decompositionSubgroup_of_forall_apply_eq_of_mem_inf_fixedField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/48bdb869-1dd6-57e7-bca3-00cffd56e138

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_mem_decompositionSubgroup_of_forall_apply_eq_of_mem_inf_fixedField

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped Pointwise

namespace Ws47
namespace DFIX

theorem isClosed_decompositionSubgroup {K L : Type*} [Field K] [Field L] [Algebra K L] [Algebra.IsIntegral K L]
    (P : ValuationSubring L) :
    IsClosed ((P.decompositionSubgroup K : Subgroup (L ≃ₐ[K] L)) : Set (L ≃ₐ[K] L)) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro σ hσ
  have hne : σ • P ≠ P := fun h => hσ (MulAction.mem_stabilizer_iff.mpr h)
  obtain ⟨x, hx⟩ : ∃ x : L, ¬ (x ∈ σ • P ↔ x ∈ P) := by
    by_contra hall
    push Not at hall
    exact hne (SetLike.ext hall)
  refine ⟨σ • (MulAction.stabilizer (L ≃ₐ[K] L) (σ⁻¹ • x) : Set (L ≃ₐ[K] L)), ?_, ?_, ?_⟩
  · intro ρ hρ hρD
    obtain ⟨s, hs, rfl⟩ := Set.mem_smul_set.mp hρ
    have hsx : s • (σ⁻¹ • x) = σ⁻¹ • x := MulAction.mem_stabilizer_iff.mp hs
    have hD : (σ • s) • P = P := MulAction.mem_stabilizer_iff.mp hρD
    apply hx
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    conv_rhs => rw [← hD, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    rw [smul_eq_mul, mul_inv_rev, mul_smul]
    have hs' : s⁻¹ • (σ⁻¹ • x) = σ⁻¹ • x := by rw [inv_smul_eq_iff, hsx]
    rw [hs']
  · exact (stabilizer_isOpen_of_isIntegral (K := K) (σ⁻¹ • x)).smul σ
  · exact Set.mem_smul_set.mpr ⟨1, MulAction.mem_stabilizer_iff.mpr (one_smul _ _), by simp⟩

end Ws47.DFIX

theorem solution
    {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (P : ValuationSubring L) (τ : L ≃ₐ[K] L)
    (h : ∀ x : L, x ∈ P → x ∈ IntermediateField.fixedField (P.decompositionSubgroup K) → τ x = x) :
    τ ∈ P.decompositionSubgroup K := by
  have hfix : τ ∈ (IntermediateField.fixedField (P.decompositionSubgroup K)).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro z hz
    rcases ValuationSubring.mem_or_inv_mem P z with hzP | hzP
    · exact h z hzP hz
    · have h1 : τ z⁻¹ = z⁻¹ := h z⁻¹ hzP ((IntermediateField.fixedField (P.decompositionSubgroup K)).inv_mem hz)
      rw [map_inv₀] at h1
      exact inv_injective h1
  have key := InfiniteGalois.fixingSubgroup_fixedField (k := K) (K := L)
    ⟨P.decompositionSubgroup K, Ws47.DFIX.isClosed_decompositionSubgroup P⟩
  rw [key] at hfix
  exact hfix

end S_ValuationSubring_mem_decompositionSubgroup_of_forall_apply_eq_of_mem_inf_fixedField
end P2MW
export P2MW.S_ValuationSubring_mem_decompositionSubgroup_of_forall_apply_eq_of_mem_inf_fixedField (solution)
