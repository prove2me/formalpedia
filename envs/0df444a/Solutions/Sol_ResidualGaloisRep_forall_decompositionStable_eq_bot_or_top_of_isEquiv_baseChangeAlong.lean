-- Prove2me | solution 1 for ResidualGaloisRep.forall_decompositionStable_eq_bot_or_top_of_isEquiv_baseChangeAlong
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/fb7b1876-a66c-55e4-9daf-66497c68aa95

import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_ResidualEquiv
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ResidualGaloisRep_forall_decompositionStable_eq_bot_or_top_of_isEquiv_baseChangeAlong

open scoped TensorProduct

namespace DichR6

open ResidualGaloisRep

variable {k : Type} [Field k]

private theorem exists_basis_forall_mem_span_baseChangeAlong' {k' : Type} [Field k']
    (ψ : k →+* k') (ρ : ResidualGaloisRep k)
    (D : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (h : ∃ b : Module.Basis (Fin 2) k ρ.V, ∀ σ ∈ D, ρ.ρ σ (b 0) ∈ k ∙ b 0) :
    ∃ b' : Module.Basis (Fin 2) k' (ρ.baseChangeAlong ψ).V,
      ∀ σ ∈ D, (ρ.baseChangeAlong ψ).ρ σ (b' 0) ∈ k' ∙ b' 0 := by
  letI : Algebra k k' := ψ.toAlgebra
  obtain ⟨b, hstab⟩ := h
  refine ⟨Algebra.TensorProduct.basis k' b, fun σ hσ => ?_⟩
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hstab σ hσ)
  show (ρ.ρ σ).baseChange k' (Algebra.TensorProduct.basis k' b 0) ∈
    k' ∙ Algebra.TensorProduct.basis k' b 0
  rw [Algebra.TensorProduct.basis_apply, LinearMap.baseChange_tmul, ← ha, TensorProduct.tmul_smul,
    algebra_compatible_smul k' a]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

private theorem exists_basis_forall_mem_span_of_equiv' {ρ₁ ρ₂ : ResidualGaloisRep k}
    (e : Equiv ρ₁ ρ₂) (D : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (h : ∃ b : Module.Basis (Fin 2) k ρ₁.V, ∀ σ ∈ D, ρ₁.ρ σ (b 0) ∈ k ∙ b 0) :
    ∃ b : Module.Basis (Fin 2) k ρ₂.V, ∀ σ ∈ D, ρ₂.ρ σ (b 0) ∈ k ∙ b 0 := by
  obtain ⟨b, hstab⟩ := h
  refine ⟨b.map e.toLinearEquiv, fun σ hσ => ?_⟩
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hstab σ hσ)
  rw [Module.Basis.map_apply, ← e.map_apply, ← ha, map_smul]
  exact Submodule.smul_mem _ a (Submodule.mem_span_singleton_self _)

private theorem span_basis_stable_ne_bot_ne_top' (ρ : ResidualGaloisRep k)
    (D : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (b : Module.Basis (Fin 2) k ρ.V) (hstab : ∀ σ ∈ D, ρ.ρ σ (b 0) ∈ k ∙ b 0) :
    (∀ σ ∈ D, ∀ v ∈ k ∙ b 0, ρ.ρ σ v ∈ k ∙ b 0) ∧ (k ∙ b 0) ≠ ⊥ ∧ (k ∙ b 0) ≠ ⊤ := by
  refine ⟨fun σ hσ v hv => ?_,
    fun hbot => b.ne_zero 0 (Submodule.span_singleton_eq_bot.mp hbot), fun htop => ?_⟩
  · obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [map_smul]
    exact Submodule.smul_mem _ a (hstab σ hσ)
  · have h1 : Module.finrank k (k ∙ b 0) = 1 := finrank_span_singleton (b.ne_zero 0)
    rw [htop, finrank_top, ρ.finrank_eq] at h1
    exact absurd h1 (by decide)

private theorem exists_basis_of_stable_ne_bot_ne_top (ρ : ResidualGaloisRep k)
    (D : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (L : Submodule k ρ.V) (hstab : ∀ σ ∈ D, ∀ v ∈ L, ρ.ρ σ v ∈ L)
    (hbot : L ≠ ⊥) (htop : L ≠ ⊤) :
    ∃ b : Module.Basis (Fin 2) k ρ.V, ∀ σ ∈ D, ρ.ρ σ (b 0) ∈ k ∙ b 0 := by
  haveI : FiniteDimensional k ρ.V := .of_finrank_eq_succ ρ.finrank_eq

  obtain ⟨v, hvL, hv0⟩ := (Submodule.ne_bot_iff _).mp hbot
  obtain ⟨w, hwL⟩ : ∃ w, w ∉ L := by
    by_contra h; push Not at h; exact htop (Submodule.eq_top_iff'.mpr h)

  have hspanle : k ∙ v ≤ L := Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hvL)
  have h1span : Module.finrank k ↥(k ∙ v) = 1 := finrank_span_singleton hv0
  have hlt : Module.finrank k L < 2 := ρ.finrank_eq ▸ Submodule.finrank_lt htop
  have hge : 1 ≤ Module.finrank k L := h1span ▸ Submodule.finrank_mono hspanle
  have hLv : L = k ∙ v :=
    (Submodule.eq_of_le_of_finrank_eq hspanle (by omega)).symm

  have hLI : LinearIndependent k ![v, w] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    rcases eq_or_ne b 0 with rfl | hb
    · exact ⟨(smul_eq_zero.mp (by simpa using hab)).resolve_right hv0, rfl⟩
    · exfalso; apply hwL
      have hbwL : b • w ∈ L := by
        rw [eq_neg_of_add_eq_zero_right hab, hLv]
        exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
      exact (Submodule.smul_mem_iff _ hb).mp hbwL
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hLI (by simp [ρ.finrank_eq]),
    fun σ hσ => ?_⟩
  rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  show ρ.ρ σ v ∈ k ∙ v
  exact hLv ▸ hstab σ hσ v hvL

end DichR6

theorem solution
    {k k' : Type} [Field k] [Field k'] (ψ : k →+* k')
    (ρ₁ : ResidualGaloisRep k) (ρ₂ : ResidualGaloisRep k')
    (he : (ρ₁.baseChangeAlong ψ).IsEquiv ρ₂) {p : ℕ}
    (hnsl : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
      ∀ L : Submodule k' ρ₂.V,
        (∀ σ ∈ P.decompositionSubgroup ℚ, ∀ v ∈ L, ρ₂.ρ σ v ∈ L) → L = ⊥ ∨ L = ⊤) :
    ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
      ∀ L : Submodule k ρ₁.V,
        (∀ σ ∈ P.decompositionSubgroup ℚ, ∀ v ∈ L, ρ₁.ρ σ v ∈ L) → L = ⊥ ∨ L = ⊤ := by
  intro P hP L hstab
  by_contra hne
  push Not at hne
  obtain ⟨hbot, htop⟩ := hne
  obtain ⟨e⟩ := he

  obtain ⟨b₂, hstab₂⟩ :=
    DichR6.exists_basis_forall_mem_span_of_equiv' e _
      (DichR6.exists_basis_forall_mem_span_baseChangeAlong' ψ ρ₁ _
        (DichR6.exists_basis_of_stable_ne_bot_ne_top ρ₁ _ L hstab hbot htop))
  obtain ⟨hstabL₂, hbot₂, htop₂⟩ :=
    DichR6.span_basis_stable_ne_bot_ne_top' ρ₂ _ b₂ hstab₂
  rcases hnsl P hP (k' ∙ b₂ 0) hstabL₂ with h | h
  · exact hbot₂ h
  · exact htop₂ h

end S_ResidualGaloisRep_forall_decompositionStable_eq_bot_or_top_of_isEquiv_baseChangeAlong
end P2MW
export P2MW.S_ResidualGaloisRep_forall_decompositionStable_eq_bot_or_top_of_isEquiv_baseChangeAlong (solution)
