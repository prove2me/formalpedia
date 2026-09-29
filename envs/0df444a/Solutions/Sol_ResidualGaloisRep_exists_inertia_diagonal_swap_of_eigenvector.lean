-- Prove2me | solution 1 for ResidualGaloisRep.exists_inertia_diagonal_swap_of_eigenvector
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/1d0a08d6-c5e9-58d4-8652-25d41b1b88f8

import Definitions.Def_GaloisRep_Residual
import Definitions.Def_FLTPrelim_Ramification
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ResidualGaloisRep_exists_inertia_diagonal_swap_of_eigenvector

namespace DichIVb

open ValuationSubring

private theorem conj_mem_inertiaSubgroupIn (P : ValuationSubring (AlgebraicClosure ℚ))
    {σ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ P.inertiaSubgroupIn ℚ)
    (hφ : φ ∈ P.decompositionSubgroup ℚ) : φ⁻¹ * σ * φ ∈ P.inertiaSubgroupIn ℚ := by
  obtain ⟨s, hs, hsσ⟩ := Subgroup.mem_map.mp hσ
  have hN : (P.inertiaSubgroup ℚ).Normal := MonoidHom.normal_ker _
  have hmem : (⟨φ, hφ⟩ : P.decompositionSubgroup ℚ)⁻¹ * s * ⟨φ, hφ⟩ ∈ P.inertiaSubgroup ℚ := by
    have h := hN.conj_mem s hs ⟨φ, hφ⟩⁻¹
    rwa [inv_inv] at h
  have himg := Subgroup.mem_map_of_mem (P.decompositionSubgroup ℚ).subtype hmem
  rw [map_mul, map_mul, map_inv, hsσ, Subgroup.subtype_apply] at himg
  exact himg

private theorem exists_basis_of_eigenvector {k' : Type} [Field k'] (ρ' : ResidualGaloisRep k')
    (P : ValuationSubring (AlgebraicClosure ℚ)) (v : ρ'.V)
    (χ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → k') (hv : v ≠ 0)
    (heig : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ρ'.ρ σ v = χ σ • v)
    {φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hφ : φ ∈ P.decompositionSubgroup ℚ)
    {σ₀ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ₀ : σ₀ ∈ P.inertiaSubgroupIn ℚ)
    (hne : χ (φ⁻¹ * σ₀ * φ) ≠ χ σ₀) :
    ∃ (b : Module.Basis (Fin 2) k' ρ'.V) (ψ ψ' : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → k'),
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, ρ'.ρ σ (b 0) = ψ σ • b 0 ∧ ρ'.ρ σ (b 1) = ψ' σ • b 1) ∧
      (∃ σ₀ ∈ P.inertiaSubgroupIn ℚ, ψ σ₀ ≠ ψ' σ₀) ∧
      (∃ φ₀ ∈ P.decompositionSubgroup ℚ, ρ'.ρ φ₀ (b 0) ∈ Submodule.span k' {b 1}) := by

  have heig' : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ρ'.ρ σ (ρ'.ρ φ v) = χ (φ⁻¹ * σ * φ) • ρ'.ρ φ v := by
    intro σ hσ
    have hconj : φ⁻¹ * σ * φ ∈ P.inertiaSubgroupIn ℚ := conj_mem_inertiaSubgroupIn P hσ hφ
    have hg : σ * φ = φ * (φ⁻¹ * σ * φ) := by
      rw [← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
    have h1 : ρ'.ρ σ (ρ'.ρ φ v) = ρ'.ρ φ (ρ'.ρ (φ⁻¹ * σ * φ) v) := by
      change (ρ'.ρ σ * ρ'.ρ φ) v = (ρ'.ρ φ * ρ'.ρ (φ⁻¹ * σ * φ)) v
      rw [← map_mul, ← map_mul, hg]
    rw [h1, heig _ hconj, map_smul]

  have hw0 : ρ'.ρ φ v ≠ 0 := by
    intro hw
    apply hv
    have h1 : ρ'.ρ φ⁻¹ (ρ'.ρ φ v) = v := by
      change (ρ'.ρ φ⁻¹ * ρ'.ρ φ) v = v
      rw [← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [← h1, hw, map_zero]

  have hind : LinearIndependent k' ![v, ρ'.ρ φ v] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have e1 : ρ'.ρ σ₀ (s • v + t • ρ'.ρ φ v) - χ σ₀ • (s • v + t • ρ'.ρ φ v) =
        (t * (χ (φ⁻¹ * σ₀ * φ) - χ σ₀)) • ρ'.ρ φ v := by
      rw [map_add, map_smul, map_smul, heig σ₀ hσ₀, heig' σ₀ hσ₀, smul_add, smul_smul, smul_smul, smul_smul,
        smul_smul, mul_sub, sub_smul, mul_comm (χ σ₀) s, mul_comm (χ σ₀) t, add_sub_add_left_eq_sub]
    rw [hst, map_zero, smul_zero, sub_self] at e1
    have ht : t = 0 := by
      rcases smul_eq_zero.mp e1.symm with h | h
      · exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hne)
      · exact absurd h hw0
    have hs : s = 0 := by
      rw [ht, zero_smul, add_zero] at hst
      exact (smul_eq_zero.mp hst).resolve_right hv
    exact ⟨hs, ht⟩

  have hcard : Fintype.card (Fin 2) = Module.finrank k' ρ'.V := by rw [Fintype.card_fin, ρ'.finrank_eq]
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hind hcard, χ, fun σ => χ (φ⁻¹ * σ * φ),
    fun σ hσ => ⟨?_, ?_⟩, ⟨σ₀, hσ₀, hne.symm⟩, ⟨φ, hφ, ?_⟩⟩
  · rw [coe_basisOfLinearIndependentOfCardEqFinrank]
    exact heig σ hσ
  · rw [coe_basisOfLinearIndependentOfCardEqFinrank]
    exact heig' σ hσ
  · rw [coe_basisOfLinearIndependentOfCardEqFinrank]
    exact Submodule.mem_span_singleton_self _

end DichIVb

theorem solution
    {k : Type} [Field k] (ρ : ResidualGaloisRep k)
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (h : ∃ (k' : Type) (_ : Field k') (ψk : k →+* k') (v : (ρ.baseChangeAlong ψk).V)
        (χ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → k'),
        v ≠ 0 ∧
        (∀ σ ∈ P.inertiaSubgroupIn ℚ, (ρ.baseChangeAlong ψk).ρ σ v = χ σ • v) ∧
        (∃ φ ∈ P.decompositionSubgroup ℚ, ∃ σ₀ ∈ P.inertiaSubgroupIn ℚ, χ (φ⁻¹ * σ₀ * φ) ≠ χ σ₀)) :
    ∃ (k' : Type) (_ : Field k') (ψk : k →+* k')
        (b : Module.Basis (Fin 2) k' (ρ.baseChangeAlong ψk).V)
        (ψ ψ' : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → k'),
        (∀ σ ∈ P.inertiaSubgroupIn ℚ,
            (ρ.baseChangeAlong ψk).ρ σ (b 0) = ψ σ • b 0 ∧
            (ρ.baseChangeAlong ψk).ρ σ (b 1) = ψ' σ • b 1) ∧
        (∃ σ₀ ∈ P.inertiaSubgroupIn ℚ, ψ σ₀ ≠ ψ' σ₀) ∧
        (∃ φ₀ ∈ P.decompositionSubgroup ℚ,
            (ρ.baseChangeAlong ψk).ρ φ₀ (b 0) ∈ Submodule.span k' {b 1}) := by
  obtain ⟨k', _, ψk, v, χ, hv, heig, φ, hφ, σ₀, hσ₀, hne⟩ := h
  exact ⟨k', ‹_›, ψk, DichIVb.exists_basis_of_eigenvector (ρ.baseChangeAlong ψk) P v χ hv heig hφ hσ₀ hne⟩

end S_ResidualGaloisRep_exists_inertia_diagonal_swap_of_eigenvector
end P2MW
export P2MW.S_ResidualGaloisRep_exists_inertia_diagonal_swap_of_eigenvector (solution)
