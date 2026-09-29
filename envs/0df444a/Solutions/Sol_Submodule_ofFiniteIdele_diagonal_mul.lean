-- Prove2me | solution 1 for Submodule.ofFiniteIdele_diagonal_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/8417edf0-0fba-54cb-ab26-d56b908afda5

import Mathlib
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Submodule_ofFiniteIdele_diagonal_mul

open scoped TensorProduct Pointwise
open IsDedekindDomain NumberField

theorem solution
    {D : Type*} [Ring D] [Algebra ℚ D]
    (Λ : Submodule ℤ D) (δ : Dˣ) (g : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    Submodule.ofFiniteIdele Λ (Submodule.finiteIdeleDiagonal D δ * g)
      = δ • Submodule.ofFiniteIdele Λ g := by
  have key : ∀ w : D, w ∈ (δ • Submodule.ofFiniteIdele Λ g : Submodule ℤ D) ↔
      ∃ y ∈ Submodule.ofFiniteIdele Λ g, (δ : D) * y = w := by
    intro w

    simp only [Submodule.mem_smul_pointwise_iff_exists, Units.smul_def, smul_eq_mul]
  ext z
  rw [Submodule.mem_ofFiniteIdele_iff, key]
  constructor
  · intro h
    obtain ⟨x, hx, hxz⟩ := AddSubgroup.mem_map.mp h
    change ((Submodule.finiteIdeleDiagonal D δ * g : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
        D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) * x = z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) at hxz
    refine ⟨(↑δ⁻¹ : D) * z, ?_, ?_⟩
    · rw [Submodule.mem_ofFiniteIdele_iff]
      refine AddSubgroup.mem_map.mpr ⟨x, hx, ?_⟩
      change ((g : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) * x
        = ((↑δ⁻¹ : D) * z) ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)
      rw [Units.val_mul, Submodule.val_finiteIdeleDiagonal_apply, mul_assoc] at hxz
      have h1 : ((↑δ⁻¹ : D) ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) *
          (((δ : D) ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) *
            (((g : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) * x))
          = ((↑δ⁻¹ : D) ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) *
            (z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) := by rw [hxz]
      rw [← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, Units.inv_mul, one_mul,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul] at h1
      rw [← h1, ← Algebra.TensorProduct.one_def, one_mul]
    · rw [← mul_assoc, Units.mul_inv, one_mul]
  · rintro ⟨w, hw, rfl⟩
    rw [Submodule.mem_ofFiniteIdele_iff] at hw
    obtain ⟨x, hx, hxw⟩ := AddSubgroup.mem_map.mp hw
    change ((g : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) * x
        = w ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) at hxw
    refine AddSubgroup.mem_map.mpr ⟨x, hx, ?_⟩
    change ((Submodule.finiteIdeleDiagonal D δ * g : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
        D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) * x = ((δ : D) * w) ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)
    rw [Units.val_mul, Submodule.val_finiteIdeleDiagonal_apply, mul_assoc, hxw,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]

end S_Submodule_ofFiniteIdele_diagonal_mul
end P2MW
export P2MW.S_Submodule_ofFiniteIdele_diagonal_mul (solution)
