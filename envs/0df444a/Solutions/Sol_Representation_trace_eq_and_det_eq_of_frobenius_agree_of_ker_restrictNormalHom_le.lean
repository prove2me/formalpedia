-- Prove2me | solution 1 for Representation.trace_eq_and_det_eq_of_frobenius_agree_of_ker_restrictNormalHom_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/44bfb04e-84f6-5c0d-86bc-c9f09528fd26

import Mathlib
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_TaylorWiles_Primes
import Theorems.Thm_FrobeniusDensity_statement
import Theorems.Thm_FrobeniusDensity_exists_frobenius_conj_pow_of_statement
import Theorems.Thm_Matrix_trace_pow_eq_of_trace_eq_of_det_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Representation_trace_eq_and_det_eq_of_frobenius_agree_of_ker_restrictNormalHom_le
p2m_attr_erase "instance" "FrobeniusDensity.liesOver_ratBelow AlgebraicClosure.Rat.isGalois"

set_option autoImplicit false

open Module LinearMap
open scoped TensorProduct

namespace P2mWs11

variable {k : Type} [CommRing k] {V : Type} [AddCommGroup V] [Module k V]

theorem trace_conj_of_inv_mul_cancel {u v : Module.End k V} (hvu : v * u = 1)
    (f : Module.End k V) : trace k V (u * f * v) = trace k V f := by
  rw [LinearMap.trace_mul_comm, ← mul_assoc, hvu, one_mul]

theorem det_conj_of_mul_inv_cancel {u v : Module.End k V} (huv : u * v = 1)
    (f : Module.End k V) : LinearMap.det (u * f * v) = LinearMap.det f := by
  rw [map_mul, map_mul, mul_comm (LinearMap.det u), mul_assoc, ← map_mul, huv, map_one,
    mul_one]

variable {G : Type} [Group G]

theorem monoidHom_apply_eq_of_mul_inv_mem_ker {M : Type} [Monoid M] (ρ : G →* M)
    {x σ : G} (h : x * σ⁻¹ ∈ ρ.ker) : ρ σ = ρ x := by
  have h1 : ρ x * ρ σ⁻¹ = 1 := by rw [← map_mul]; exact h
  have h2 : ρ σ⁻¹ * ρ σ = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  calc ρ σ = (ρ x * ρ σ⁻¹) * ρ σ := by rw [h1, one_mul]
    _ = ρ x * (ρ σ⁻¹ * ρ σ) := mul_assoc _ _ _
    _ = ρ x := by rw [h2, mul_one]

theorem repr_inv_mul_cancel (ρ : Representation k G V) (g : G) : ρ g⁻¹ * ρ g = 1 := by
  rw [← map_mul, inv_mul_cancel, map_one]

theorem repr_mul_inv_cancel (ρ : Representation k G V) (g : G) : ρ g * ρ g⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel, map_one]

end P2mWs11

namespace P2mWs11

private theorem _root_.P2mWs11.trace_pow_eq_of_trace_eq_of_det_eq {k : Type} [Field k]
    {V₁ : Type} [AddCommGroup V₁] [Module k V₁] {V₂ : Type} [AddCommGroup V₂] [Module k V₂]
    [Module.Finite k V₁] [Module.Finite k V₂]
    (h₁ : Module.finrank k V₁ = 2) (h₂ : Module.finrank k V₂ = 2)
    {f₁ : V₁ →ₗ[k] V₁} {f₂ : V₂ →ₗ[k] V₂}
    (htr : trace k V₁ f₁ = trace k V₂ f₂) (hdet : LinearMap.det f₁ = LinearMap.det f₂)
    (n : ℕ) : trace k V₁ (f₁ ^ n) = trace k V₂ (f₂ ^ n) := by
  classical
  let b₁ : Basis (Fin 2) k V₁ := Module.finBasisOfFinrankEq k V₁ h₁
  let b₂ : Basis (Fin 2) k V₂ := Module.finBasisOfFinrankEq k V₂ h₂
  have e₁ : ∀ g : V₁ →ₗ[k] V₁, trace k V₁ g = (LinearMap.toMatrix b₁ b₁ g).trace := fun g =>
    LinearMap.trace_eq_matrix_trace k b₁ g
  have e₂ : ∀ g : V₂ →ₗ[k] V₂, trace k V₂ g = (LinearMap.toMatrix b₂ b₂ g).trace := fun g =>
    LinearMap.trace_eq_matrix_trace k b₂ g
  rw [e₁, e₂, ← LinearMap.toMatrix_pow, ← LinearMap.toMatrix_pow]
  exact Matrix.trace_pow_eq_of_trace_eq_of_det_eq
    (by rw [← e₁, ← e₂]; exact htr)
    (by rw [LinearMap.det_toMatrix, LinearMap.det_toMatrix]; exact hdet) n

p2m_export "P2mWs11" "trace_pow_eq_of_trace_eq_of_det_eq"

private theorem _root_.P2mWs11.baseChange_pow {k K : Type} [CommRing k] [CommRing K] [Algebra k K]
    {V : Type} [AddCommGroup V] [Module k V] (f : Module.End k V) (n : ℕ) :
    (f ^ n).baseChange K = (f.baseChange K) ^ n := by
  induction n with
  | zero => simp [Module.End.one_eq_id, LinearMap.baseChange_id]
  | succ n ih => rw [pow_succ, pow_succ, Module.End.mul_eq_comp, Module.End.mul_eq_comp, LinearMap.baseChange_comp, ih]

p2m_export "P2mWs11" "baseChange_pow"
end P2mWs11

open P2mWs11 in
theorem solution
    {k K : Type} [Field k] [Field K] [Algebra k K]
    {V₁ : Type} [AddCommGroup V₁] [Module k V₁] {V₂ : Type} [AddCommGroup V₂] [Module K V₂]
    (ρ₁ : Representation k (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) V₁)
    (ρ₂ : Representation K (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) V₂)
    (h₁ : Module.finrank k V₁ = 2) (h₂ : Module.finrank K V₂ = 2)
    (F : Type) [Field F] [NumberField F] [IsGalois ℚ F]
    [Algebra F (AlgebraicClosure ℚ)] [IsScalarTower ℚ F (AlgebraicClosure ℚ)]
    (hker : (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).ker ≤ ρ₁.ker ⊓ ρ₂.ker)
    (S : Finset ℕ)
    (htr : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt τ ℓ →
          algebraMap k K (LinearMap.trace k V₁ (ρ₁ τ)) = LinearMap.trace K V₂ (ρ₂ τ))
    (hdet : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt τ ℓ →
          algebraMap k K (LinearMap.det (ρ₁ τ)) = LinearMap.det (ρ₂ τ))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    algebraMap k K (LinearMap.trace k V₁ (ρ₁ σ)) = LinearMap.trace K V₂ (ρ₂ σ) ∧
      algebraMap k K (LinearMap.det (ρ₁ σ)) = LinearMap.det (ρ₂ σ) := by
  classical
  have hV₁ : FiniteDimensional k V₁ := .of_finrank_pos (by omega)
  have hV₂ : FiniteDimensional K V₂ := .of_finrank_pos (by omega)
  have hfrK : Module.finrank K (K ⊗[k] V₁) = 2 := by
    rw [Module.finrank_baseChange]; exact h₁
  have hVK : FiniteDimensional K (K ⊗[k] V₁) := .of_finrank_pos (by omega)

  let ι : F →ₐ[ℚ] AlgebraicClosure ℚ := IsScalarTower.toAlgHom ℚ F (AlgebraicClosure ℚ)
  let L : IntermediateField ℚ (AlgebraicClosure ℚ) := ι.fieldRange
  haveI : FiniteDimensional ℚ L := Module.Finite.equiv
    (((IntermediateField.topEquiv (F := ℚ) (E := F)).symm.trans (IntermediateField.equivMap ⊤ ι)).trans
      (IntermediateField.equivOfEq (AlgHom.fieldRange_eq_map ι).symm)).toLinearEquiv
  have hFD : ∀ (M : Type) [Field M] [NumberField M] [IsGalois ℚ M], FrobeniusDensity.Statement M :=
    fun M _ _ _ => FrobeniusDensity.statement M
  obtain ⟨ℓ, hℓ, hℓS, A, τ, γ, j, hA, hτ, hLfix⟩ :=
    FrobeniusDensity.exists_frobenius_conj_pow_of_statement hFD L σ S

  have hmemL : ∀ y : F, algebraMap F (AlgebraicClosure ℚ) y ∈ L := fun y =>
    AlgHom.mem_fieldRange.mpr ⟨y, rfl⟩
  have hfixF : ∀ y : F, (γ * τ ^ j * γ⁻¹ * σ⁻¹) (algebraMap F (AlgebraicClosure ℚ) y)
      = algebraMap F (AlgebraicClosure ℚ) y := by
    intro y

    have hy' : σ⁻¹ (algebraMap F (AlgebraicClosure ℚ) y) ∈ L := by
      have := AlgEquiv.restrictNormal_commutes σ⁻¹ F y
      rw [← this]
      exact hmemL _
    have h := hLfix _ hy'

    rw [AlgEquiv.mul_apply, ← h, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  have hkerMem : γ * τ ^ j * γ⁻¹ * σ⁻¹ ∈
      (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).ker := by
    rw [MonoidHom.mem_ker]
    apply AlgEquiv.ext
    intro y
    apply (algebraMap F (AlgebraicClosure ℚ)).injective
    have hc := AlgEquiv.restrictNormal_commutes (γ * τ ^ j * γ⁻¹ * σ⁻¹) F y
    change algebraMap F (AlgebraicClosure ℚ) (((γ * τ ^ j * γ⁻¹ * σ⁻¹).restrictNormal F) y)
      = algebraMap F (AlgebraicClosure ℚ) ((1 : F ≃ₐ[ℚ] F) y)
    rw [AlgEquiv.one_apply, hc]
    exact hfixF y
  have hmem : γ * τ ^ j * γ⁻¹ * σ⁻¹ ∈ ρ₁.ker ⊓ ρ₂.ker := hker hkerMem

  have key₁ : ρ₁ σ = ρ₁ γ * (ρ₁ τ) ^ j * ρ₁ γ⁻¹ := by
    rw [monoidHom_apply_eq_of_mul_inv_mem_ker ρ₁ (Subgroup.mem_inf.mp hmem).1, map_mul,
      map_mul, map_pow]
  have key₂ : ρ₂ σ = ρ₂ γ * (ρ₂ τ) ^ j * ρ₂ γ⁻¹ := by
    rw [monoidHom_apply_eq_of_mul_inv_mem_ker ρ₂ (Subgroup.mem_inf.mp hmem).2, map_mul,
      map_mul, map_pow]
  have htrτ : algebraMap k K (trace k V₁ (ρ₁ τ)) = trace K V₂ (ρ₂ τ) := htr ℓ hℓ hℓS A hA τ hτ
  have hdetτ : algebraMap k K (LinearMap.det (ρ₁ τ)) = LinearMap.det (ρ₂ τ) :=
    hdet ℓ hℓ hℓS A hA τ hτ
  constructor
  · rw [key₁, key₂, trace_conj_of_inv_mul_cancel (repr_inv_mul_cancel ρ₁ γ),
      trace_conj_of_inv_mul_cancel (repr_inv_mul_cancel ρ₂ γ)]
    have hbase : algebraMap k K (trace k V₁ ((ρ₁ τ) ^ j))
        = trace K (K ⊗[k] V₁) (((ρ₁ τ).baseChange K) ^ j) := by
      rw [← LinearMap.baseChange_pow, LinearMap.trace_baseChange]
    rw [hbase]
    refine trace_pow_eq_of_trace_eq_of_det_eq hfrK h₂ ?_ ?_ j
    · rw [LinearMap.trace_baseChange]; exact htrτ
    · rw [LinearMap.det_baseChange]; exact hdetτ
  · rw [key₁, key₂, det_conj_of_mul_inv_cancel (repr_mul_inv_cancel ρ₁ γ),
      det_conj_of_mul_inv_cancel (repr_mul_inv_cancel ρ₂ γ)]
    simp only [map_pow]
    rw [hdetτ]

end S_Representation_trace_eq_and_det_eq_of_frobenius_agree_of_ker_restrictNormalHom_le
end P2MW
export P2MW.S_Representation_trace_eq_and_det_eq_of_frobenius_agree_of_ker_restrictNormalHom_le (solution)
