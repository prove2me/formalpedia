-- Prove2me | solution 1 for QuaternionAlgebra.IsEichlerOrder.levelIdentity_iff_exists_mem_levelHeckeUSet_conj_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/6aac0c57-a461-5c5f-8251-9b8c64578652

import Mathlib
import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Theorems.Thm_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_isUnit_of_ne_zero
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_exists_mem_levelHeckeUSet_coe_eq_tmul_iff
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_levelIdentity_iff_not_conj_eq_and_not_conj_le_of_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsEichlerOrder_levelIdentity_iff_exists_mem_levelHeckeUSet_conj_of_dvd
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

open scoped Quaternion TensorProduct NumberField MatrixGroups Pointwise
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

namespace HeckeDictReduce

theorem dictA
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime]
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (x : (ℍ[ℚ, a, b])ˣ) (hxR : (x : ℍ[ℚ, a, b]) ∈ R) (hnx : nrd (x : ℍ[ℚ, a, b]) = (ℓ : ℚ)) :
    (∃ h ∈ levelHeckeUSet Λ R ℓ,
        (h : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = (x : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) ↔
      (¬ ∀ z : ℍ[ℚ, a, b], ((x⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * z * (x : ℍ[ℚ, a, b]) ∈ R ↔ z ∈ R) ∧
      (¬ ∀ r ∈ R, ((x⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * r * (x : ℍ[ℚ, a, b]) ∈ Λ) :=
  QuaternionAlgebra.IsEichlerOrder.exists_mem_levelHeckeUSet_coe_eq_tmul_iff hB Λ hΛ R hR hRΛ ℓ hℓ x hxR hnx

theorem trichB
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (hN : Squarefree N) (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (J' : Submodule ℤ ℍ[ℚ, a, b])
    (hJ' : Λ ≤ J' ∧ (∀ x ∈ Λ, ∀ y ∈ J', x * y ∈ J') ∧ (∀ y ∈ J', ((N : ℤ) • y) ∈ Λ) ∧
      Λ.toAddSubgroup.relIndex J'.toAddSubgroup = N ^ 2 ∧ (∀ x ∈ Λ, x ∈ R ↔ ∀ y ∈ J', y * x ∈ J'))
    (w : (ℍ[ℚ, a, b])ˣ) (hwR : (w : ℍ[ℚ, a, b]) ∈ R) (hwn : nrd (w : ℍ[ℚ, a, b]) = (N : ℚ))
    (hwnorm : ∀ x : ℍ[ℚ, a, b], x ∈ R ↔ (w : ℍ[ℚ, a, b]) * x * ((w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ∈ R)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N) (t : ℍ[ℚ, a, b]) (ht : t ∈ R) (hnt : nrd t = (ℓ : ℚ))
    (T : (ℍ[ℚ, a, b])ˣ) (hT : (T : ℍ[ℚ, a, b]) = t) :
    (∀ x : ℍ[ℚ, a, b], (∃ j ∈ J', ∃ m ∈ Λ, (ℓ : ℤ) • j + m * t = x) ↔ ∃ j ∈ J', j * t = x) ↔
      ((¬ ∀ z : ℍ[ℚ, a, b],
          (((w * T * w⁻¹)⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * z * ((w * T * w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ∈ R ↔ z ∈ R) ∧
        (¬ ∀ r ∈ R,
          (((w * T * w⁻¹)⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * r * ((w * T * w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ∈ Λ)) :=
  QuaternionAlgebra.IsEichlerOrder.levelIdentity_iff_not_conj_eq_and_not_conj_le_of_dvd hqN hq'N hqq' hB Λ hΛ hN R hR hRΛ J' hJ' w hwR hwn hwnorm ℓ hℓ hℓN t ht hnt T hT

end HeckeDictReduce

open HeckeDictReduce in
theorem solution
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (hN : Squarefree N) (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (J' : Submodule ℤ ℍ[ℚ, a, b])
    (hJ' : Λ ≤ J' ∧ (∀ x ∈ Λ, ∀ y ∈ J', x * y ∈ J') ∧ (∀ y ∈ J', ((N : ℤ) • y) ∈ Λ) ∧
      Λ.toAddSubgroup.relIndex J'.toAddSubgroup = N ^ 2 ∧ (∀ x ∈ Λ, x ∈ R ↔ ∀ y ∈ J', y * x ∈ J'))
    (w : (ℍ[ℚ, a, b])ˣ) (hwR : (w : ℍ[ℚ, a, b]) ∈ R) (hwn : nrd (w : ℍ[ℚ, a, b]) = (N : ℚ))
    (hwnorm : ∀ x : ℍ[ℚ, a, b], x ∈ R ↔ (w : ℍ[ℚ, a, b]) * x * ((w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ∈ R)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N) (t : ℍ[ℚ, a, b]) (ht : t ∈ R) (hnt : nrd t = (ℓ : ℚ)) :
    (∀ x : ℍ[ℚ, a, b], (∃ j ∈ J', ∃ m ∈ Λ, (ℓ : ℤ) • j + m * t = x) ↔ ∃ j ∈ J', j * t = x) ↔
      ∃ h ∈ levelHeckeUSet Λ R ℓ,
        (h : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = ((w : ℍ[ℚ, a, b]) * t * ((w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b])) ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) := by
  have hℓ0 : (ℓ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hℓ.ne_zero
  have ht0 : t ≠ 0 := by intro h; apply hℓ0; rw [← hnt, h, nrd_zero]
  obtain ⟨T, hT⟩ := QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt.isUnit_of_ne_zero hB t ht0
  have hx : ((w * T * w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) = (w : ℍ[ℚ, a, b]) * t * ((w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) := by
    rw [Units.val_mul, Units.val_mul, hT]
  have hxR : ((w * T * w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ∈ R := by rw [hx]; exact (hwnorm t).1 ht
  have hnrdmul : ∀ x y : ℍ[ℚ, a, b], nrd (x * y) = nrd x * nrd y := by
    intro x y
    obtain ⟨x₀, x₁, x₂, x₃⟩ := x
    obtain ⟨y₀, y₁, y₂, y₃⟩ := y
    simp only [QuaternionAlgebra.mk_mul_mk, nrd_mk]; ring
  have hN0 : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hnx : nrd ((w * T * w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) = (ℓ : ℚ) := by
    have hwinv : nrd ((w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) = (N : ℚ)⁻¹ := by
      have h1 : nrd (w : ℍ[ℚ, a, b]) * nrd ((w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) = 1 := by
        rw [← hnrdmul, Units.mul_inv, nrd_one]
      rw [hwn] at h1
      exact (eq_inv_of_mul_eq_one_right h1)
    rw [hx, hnrdmul, hnrdmul, hwn, hnt, hwinv]; field_simp
  rw [← hx, dictA hB Λ hΛ R hR hRΛ ℓ hℓ (w * T * w⁻¹) hxR hnx]
  exact trichB hqN hq'N hqq' hB Λ hΛ hN R hR hRΛ J' hJ' w hwR hwn hwnorm ℓ hℓ hℓN t ht hnt T hT

end S_QuaternionAlgebra_IsEichlerOrder_levelIdentity_iff_exists_mem_levelHeckeUSet_conj_of_dvd
end P2MW
export P2MW.S_QuaternionAlgebra_IsEichlerOrder_levelIdentity_iff_exists_mem_levelHeckeUSet_conj_of_dvd (solution)
