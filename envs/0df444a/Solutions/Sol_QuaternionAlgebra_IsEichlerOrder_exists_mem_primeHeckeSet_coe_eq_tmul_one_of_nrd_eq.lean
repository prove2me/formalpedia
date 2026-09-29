-- Prove2me | solution 1 for QuaternionAlgebra.IsEichlerOrder.exists_mem_primeHeckeSet_coe_eq_tmul_one_of_nrd_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/7f1cd272-784d-513b-b8d6-ffc11b8a1dc2

import Mathlib
import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_Submodule_LocalBox
import Definitions.Def_Submodule_FiniteAdeleBox
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_intCast_eq_nrd_and_exists_intCast_eq_trd
import Theorems.Thm_Submodule_mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox
import Theorems.Thm_Submodule_ofFiniteIdele_one
import Theorems.Thm_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_isUnit_of_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_mem_primeHeckeSet_coe_eq_tmul_one_of_nrd_eq

set_option autoImplicit false

open scoped Quaternion TensorProduct NumberField MatrixGroups Pointwise
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

noncomputable section

namespace HeckeGlobalDict

variable {a b : ℚ}

abbrev AB (a b : ℚ) := ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ

theorem tmul_one_mem_finiteAdeleBox_iff {O : Submodule ℤ ℍ[ℚ, a, b]} (hO : IsOrder O) (z : ℍ[ℚ, a, b]) :
    z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.finiteAdeleBox O ↔ z ∈ O := by
  constructor
  · intro h
    rw [← Submodule.ofFiniteIdele_one O hO.fg hO.spanTop, Submodule.mem_ofFiniteIdele_iff, AddSubgroup.mem_map]
    exact ⟨_, h, by simp⟩
  · intro hz
    exact AddSubgroup.subset_closure ⟨z, hz, 1, fun v => by change (1 : v.adicCompletion ℚ) ∈ _; exact one_mem _, rfl⟩

theorem star_mem {O : Submodule ℤ ℍ[ℚ, a, b]} (hO : IsOrder O) {x : ℍ[ℚ, a, b]} (hx : x ∈ O) : star x ∈ O := by
  obtain ⟨t, ht⟩ := (hO.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hx).2
  have e : star x = ((trd x : ℚ) : ℍ[ℚ, a, b]) - x := by rw [← add_star_eq_coe_trd]; abel
  rw [e, ← ht]
  refine sub_mem ?_ hx
  have : (((t : ℤ) : ℚ) : ℍ[ℚ, a, b]) = t • (1 : ℍ[ℚ, a, b]) := by
    rw [← Int.cast_smul_eq_zsmul ℚ, ← coe_mul_eq_smul, mul_one]
  rw [this]; exact O.smul_mem t hO.one_mem

theorem nrd_mul' (x y : ℍ[ℚ, a, b]) : nrd (x * y) = nrd x * nrd y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [QuaternionAlgebra.mk_mul_mk, nrd_mk]
  ring

theorem nrd_smul' (c : ℚ) (x : ℍ[ℚ, a, b]) : nrd (c • x) = c ^ 2 * nrd x := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  simp only [nrd, QuaternionAlgebra.re_smul, QuaternionAlgebra.imI_smul, QuaternionAlgebra.imJ_smul,
    QuaternionAlgebra.imK_smul, smul_eq_mul]
  ring

theorem nrd_ne_inv_prime {O : Submodule ℤ ℍ[ℚ, a, b]} (hO : IsOrder O) {ℓ : ℕ} (hℓ : ℓ.Prime) {y : ℍ[ℚ, a, b]}
    (hy : y ∈ O) (h : nrd y = (ℓ : ℚ)⁻¹) : False := by
  obtain ⟨m, hm⟩ := (hO.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hy).1
  rw [h] at hm
  have hℓ0 : (ℓ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hℓ.ne_zero
  have h1 : (m : ℚ) * ℓ = 1 := by rw [hm, inv_mul_cancel₀ hℓ0]
  have h2 : m * (ℓ : ℤ) = 1 := by exact_mod_cast h1
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' h2 with ⟨-, h3⟩ | ⟨-, h3⟩
  · have : ℓ = 1 := by exact_mod_cast h3
    exact hℓ.one_lt.ne' this
  · have : (0 : ℤ) ≤ (ℓ : ℤ) := Int.natCast_nonneg ℓ
    omega

end HeckeGlobalDict

end

open HeckeGlobalDict in
theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    {N : ℕ} [NeZero N] (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (x : ℍ[ℚ, a, b]) (hx : x ∈ R) (hnrd : nrd x = (ℓ : ℚ)) :
    ∃ h ∈ primeHeckeSet R ℓ,
      (h : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = x ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) := by
  classical
  have hRo : IsOrder R := hR.isOrder
  have hℓ0 : (ℓ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hℓ.ne_zero
  have hx0 : x ≠ 0 := by intro h; apply hℓ0; rw [← hnrd, h, nrd_zero]
  obtain ⟨X, hX⟩ := QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt.isUnit_of_ne_zero hB x hx0
  set hxI : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ := Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] X with hhx
  have hval : (hxI : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = x ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) := by
    rw [hhx, Submodule.val_finiteIdeleDiagonal_apply, hX]
  have hinv : ((hxI⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
      ((X⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) := by
    rw [hhx, ← map_inv, Submodule.val_finiteIdeleDiagonal_apply]
  have hstarx : star x = (ℓ : ℚ) • ((X⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) := by
    have h1 : x * star x = ((ℓ : ℚ) : ℍ[ℚ, a, b]) := by rw [mul_star_eq_coe_nrd, hnrd]
    calc star x = ((X⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * ((X : ℍ[ℚ, a, b]) * star x) := by
          rw [Units.inv_mul_cancel_left]
      _ = _ := by rw [hX, h1, ← coe_commutes, coe_mul_eq_smul]
  refine ⟨hxI, ?_, hval⟩
  rw [mem_primeHeckeSet_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hval]; exact (tmul_one_mem_finiteAdeleBox_iff hRo _).2 hx
  · rw [hinv, TensorProduct.smul_tmul', ← hstarx]
    exact (tmul_one_mem_finiteAdeleBox_iff hRo _).2 (star_mem hRo hx)
  · rw [hinv, tmul_one_mem_finiteAdeleBox_iff hRo]
    intro hmem
    apply nrd_ne_inv_prime hRo hℓ hmem
    have h1 : nrd (X : ℍ[ℚ, a, b]) * nrd ((X⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) = 1 := by
      rw [← nrd_mul', Units.mul_inv, nrd_one]
    rw [hX, hnrd] at h1
    exact eq_inv_of_mul_eq_one_right h1
  · rw [hval, TensorProduct.smul_tmul', tmul_one_mem_finiteAdeleBox_iff hRo]
    intro hmem
    apply nrd_ne_inv_prime hRo hℓ hmem
    rw [nrd_smul', hnrd]; field_simp

end S_QuaternionAlgebra_IsEichlerOrder_exists_mem_primeHeckeSet_coe_eq_tmul_one_of_nrd_eq
end P2MW
export P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_mem_primeHeckeSet_coe_eq_tmul_one_of_nrd_eq (solution)
