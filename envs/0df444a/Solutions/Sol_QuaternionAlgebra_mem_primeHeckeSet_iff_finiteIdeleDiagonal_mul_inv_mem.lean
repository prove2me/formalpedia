-- Prove2me | solution 1 for QuaternionAlgebra.mem_primeHeckeSet_iff_finiteIdeleDiagonal_mul_inv_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/bdfbec68-60fa-5611-8343-68b5871e40ef

import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_mem_primeHeckeSet_iff_finiteIdeleDiagonal_mul_inv_mem

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem solution
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (ℓ : ℕ) [Fact ℓ.Prime]
    (h : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    h ∈ QuaternionAlgebra.primeHeckeSet Λ ℓ ↔
      Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]
          (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom
            (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero))) * h⁻¹ ∈
        QuaternionAlgebra.primeHeckeSet Λ ℓ := by
  set T := Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom
      (Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero))) with hTdef
  have hℓ0 : (ℓ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero
  have hT : (T : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = (ℓ : ℚ) • (1 : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) := by
    change (algebraMap ℚ ℍ[ℚ, a, b] (ℓ : ℚ)) ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) = _
    rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul', Algebra.TensorProduct.one_def]
  have hTi : ((T⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
      (ℓ : ℚ)⁻¹ • (1 : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) := by
    rw [hTdef, ← map_inv, ← map_inv]
    change (algebraMap ℚ ℍ[ℚ, a, b]
      (((Units.mk0 (ℓ : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero))⁻¹ : ℚˣ) : ℚ)) ⊗ₜ[ℚ]
        (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) = _
    rw [Units.val_inv_eq_inv_val, Units.val_mk0, Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul',
      Algebra.TensorProduct.one_def]
  have e1 : ((T * h⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
      (ℓ : ℚ) • ((h⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) := by
    rw [Units.val_mul, hT, smul_mul_assoc, one_mul]
  have e3 : (((T * h⁻¹)⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
      (ℓ : ℚ)⁻¹ • (h : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) := by
    rw [mul_inv_rev, inv_inv, Units.val_mul, hTi, mul_smul_comm, mul_one]
  have e2 : (ℓ : ℚ) • (((T * h⁻¹)⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
      (h : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) := by
    rw [e3, smul_smul, mul_inv_cancel₀ hℓ0, one_smul]
  have e4 : (ℓ : ℚ)⁻¹ • ((T * h⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
      ((h⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) := by
    rw [e1, smul_smul, inv_mul_cancel₀ hℓ0, one_smul]
  rw [QuaternionAlgebra.mem_primeHeckeSet_iff, QuaternionAlgebra.mem_primeHeckeSet_iff, e2, e4, e3, e1]
  tauto

end S_QuaternionAlgebra_mem_primeHeckeSet_iff_finiteIdeleDiagonal_mul_inv_mem
end P2MW
export P2MW.S_QuaternionAlgebra_mem_primeHeckeSet_iff_finiteIdeleDiagonal_mul_inv_mem (solution)
