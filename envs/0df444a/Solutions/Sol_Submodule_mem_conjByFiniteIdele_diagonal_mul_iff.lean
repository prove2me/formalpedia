-- Prove2me | solution 1 for Submodule.mem_conjByFiniteIdele_diagonal_mul_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/e8da7e45-23f9-5c88-a18a-37add42bedd2

import Mathlib
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Submodule_mem_conjByFiniteIdele_diagonal_mul_iff

open scoped TensorProduct Pointwise
open IsDedekindDomain NumberField

theorem r7_mem_conjByFiniteIdele_iff' {D : Type*} [Ring D] [Algebra ℚ D] (Λ : Submodule ℤ D)
    (g : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (z : D) :
    z ∈ Submodule.conjByFiniteIdele Λ g ↔
      ∃ u ∈ Λ.finiteAdeleBox, (g : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) * u * ((g⁻¹ : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)
        = z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) := by
  rw [Submodule.mem_conjByFiniteIdele_iff, AddSubgroup.mem_map]
  rfl

theorem solution
    {D : Type*} [Ring D] [Algebra ℚ D] (Λ : Submodule ℤ D) (γ : Dˣ) (β : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (z : D) :
    z ∈ Submodule.conjByFiniteIdele Λ (Submodule.finiteIdeleDiagonal D γ * β) ↔
      (↑γ⁻¹ : D) * z * γ ∈ Submodule.conjByFiniteIdele Λ β := by
  rw [r7_mem_conjByFiniteIdele_iff', r7_mem_conjByFiniteIdele_iff']

  have hγγ : ((↑γ⁻¹ : D) ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) * ((γ : D) ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ))
      = 1 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, Units.inv_mul, one_mul, Algebra.TensorProduct.one_def]
  have hγγ' : ((γ : D) ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) * ((↑γ⁻¹ : D) ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ))
      = 1 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, Units.mul_inv, one_mul, Algebra.TensorProduct.one_def]
  constructor
  · rintro ⟨u, hu, hz⟩
    refine ⟨u, hu, ?_⟩

    have h2 := congrArg (fun t => ((↑γ⁻¹ : D) ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) * t *
      ((γ : D) ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ))) hz
    rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul,
      mul_inv_rev, Units.val_mul, Units.val_mul, ← map_inv, Submodule.val_finiteIdeleDiagonal_apply,
      Submodule.val_finiteIdeleDiagonal_apply] at h2
    rw [← h2]
    simp only [mul_assoc]
    rw [← mul_assoc ((↑γ⁻¹ : D) ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)), hγγ, one_mul, mul_one]
  · rintro ⟨u, hu, hz⟩
    refine ⟨u, hu, ?_⟩
    rw [mul_inv_rev, Units.val_mul, Units.val_mul, ← map_inv, Submodule.val_finiteIdeleDiagonal_apply,
      Submodule.val_finiteIdeleDiagonal_apply]
    have h2 := congrArg (fun t => ((γ : D) ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) * t *
      ((↑γ⁻¹ : D) ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ))) hz
    rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul] at h2
    have h3 : (γ : D) * ((↑γ⁻¹ : D) * z * γ) * (↑γ⁻¹ : D) = z := by
      rw [← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul, mul_assoc, Units.mul_inv, mul_one]
    rw [h3] at h2
    rw [← h2]
    simp only [mul_assoc]

end S_Submodule_mem_conjByFiniteIdele_diagonal_mul_iff
end P2MW
export P2MW.S_Submodule_mem_conjByFiniteIdele_diagonal_mul_iff (solution)
