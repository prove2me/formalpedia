-- Prove2me | solution 1 for QuaternionAlgebra.IsMaximalOrder.exists_ringEquiv_mem_localBox_iff_of_isIndefiniteRamifiedExactlyAt_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/8c8a7bcb-2332-5426-9c3e-48102036ca3a

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_LocalBox
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_Submodule_FiniteAdeleBox
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_localBox_iff_generalLinearGroup_conj_mem_adicCompletionIntegers
import Theorems.Thm_QuaternionAlgebra_exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
import Theorems.Thm_QuaternionAlgebra_nonempty_algEquiv_matrix_of_ne_zero_of_not_isUnit
import Theorems.Thm_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_isUnit_of_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_ringEquiv_mem_localBox_iff_of_isIndefiniteRamifiedExactlyAt_of_prime
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

namespace ASM21
namespace MLS

def conjEquiv {n : Type} [Fintype n] [DecidableEq n] {K : Type} [CommRing K] (h : GL n K) :
    Matrix n n K ≃+* Matrix n n K where
  toFun X := ((h⁻¹ : GL n K) : Matrix n n K) * X * (h : Matrix n n K)
  invFun X := (h : Matrix n n K) * X * ((h⁻¹ : GL n K) : Matrix n n K)
  left_inv X := by
    show (h : Matrix n n K) * (((h⁻¹ : GL n K) : Matrix n n K) * X * (h : Matrix n n K)) * ((h⁻¹ : GL n K) : Matrix n n K) = X
    rw [← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul, mul_assoc, Units.mul_inv, mul_one]
  right_inv X := by
    show ((h⁻¹ : GL n K) : Matrix n n K) * ((h : Matrix n n K) * X * ((h⁻¹ : GL n K) : Matrix n n K)) * (h : Matrix n n K) = X
    rw [← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul, mul_assoc, Units.inv_mul, mul_one]
  map_mul' X Y := by
    show ((h⁻¹ : GL n K) : Matrix n n K) * (X * Y) * (h : Matrix n n K) =
      (((h⁻¹ : GL n K) : Matrix n n K) * X * (h : Matrix n n K)) * (((h⁻¹ : GL n K) : Matrix n n K) * Y * (h : Matrix n n K))
    simp only [mul_assoc, Units.mul_inv_cancel_left]
  map_add' X Y := by
    show ((h⁻¹ : GL n K) : Matrix n n K) * (X + Y) * (h : Matrix n n K) =
      ((h⁻¹ : GL n K) : Matrix n n K) * X * (h : Matrix n n K) + ((h⁻¹ : GL n K) : Matrix n n K) * Y * (h : Matrix n n K)
    rw [mul_add, add_mul]

theorem conjEquiv_apply {n : Type} [Fintype n] [DecidableEq n] {K : Type} [CommRing K] (h : GL n K) (X : Matrix n n K) :
    conjEquiv h X = ((h⁻¹ : GL n K) : Matrix n n K) * X * (h : Matrix n n K) := rfl

end ASM21.MLS

theorem solution
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hB : QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt a b q q')
    {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsMaximalOrder Λ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hqv : (q : 𝓞 ℚ) ∉ v.asIdeal) (hq'v : (q' : 𝓞 ℚ) ∉ v.asIdeal) :
    ∃ φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ),
      (∀ r : v.adicCompletion ℚ,
        φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) ∧
      ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ,
        x ∈ Submodule.localBox Λ v ↔ ∀ i j, φ x i j ∈ v.adicCompletionIntegers ℚ := by
  classical

  have hdiv := fun (x : ℍ[ℚ, a, b]) (hx : x ≠ 0) => QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt.isUnit_of_ne_zero hB x hx
  have ha : a ≠ 0 := by
    intro ha0
    have hi : (⟨0, 1, 0, 0⟩ : ℍ[ℚ, a, b]) ≠ 0 := fun h => by simpa using congrArg QuaternionAlgebra.imI h
    have hu := (hdiv _ hi).mul (hdiv _ hi)
    have hsq : (⟨0, 1, 0, 0⟩ : ℍ[ℚ, a, b]) * ⟨0, 1, 0, 0⟩ = 0 := by
      ext <;> simp [ha0]
    rw [hsq] at hu
    exact not_isUnit_zero hu
  have hb : b ≠ 0 := by
    intro hb0
    have hj : (⟨0, 0, 1, 0⟩ : ℍ[ℚ, a, b]) ≠ 0 := fun h => by simpa using congrArg QuaternionAlgebra.imJ h
    have hu := (hdiv _ hj).mul (hdiv _ hj)
    have hsq : (⟨0, 0, 1, 0⟩ : ℍ[ℚ, a, b]) * ⟨0, 0, 1, 0⟩ = 0 := by
      ext <;> simp [hb0]
    rw [hsq] at hu
    exact not_isUnit_zero hu

  have hnd : ∃ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 ∧ ¬ IsUnit x := by
    have h := (hB.2 v).not.2 (not_or.2 ⟨hqv, hq'v⟩)
    push_neg at h
    exact h
  obtain ⟨x, hx0, hxu⟩ := hnd

  set K := v.adicCompletion ℚ with hK
  obtain ⟨φ₁, -, -⟩ := QuaternionAlgebra.exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
    (R := ℚ) (S := K) (c₁ := a) (c₂ := (0 : ℚ)) (c₃ := b) (d₁ := algebraMap ℚ K a) (d₂ := (0 : K)) (d₃ := algebraMap ℚ K b)
    rfl (map_zero _) rfl (AlgEquiv.refl : ℍ[K, algebraMap ℚ K a, (0 : K), algebraMap ℚ K b] ≃ₐ[K] _)
  have hx1 : φ₁ x ≠ 0 := fun h => hx0 (by simpa using congrArg φ₁.symm h)
  have hx1u : ¬ IsUnit (φ₁ x) := fun h => hxu (by simpa using h.map φ₁.symm)
  have haK : algebraMap ℚ K a ≠ 0 := by rwa [map_ne_zero_iff _ (algebraMap ℚ K).injective]
  have hbK : algebraMap ℚ K b ≠ 0 := by rwa [map_ne_zero_iff _ (algebraMap ℚ K).injective]
  haveI : NeZero (2 : K) := ⟨by
    rw [show (2 : K) = algebraMap ℚ K 2 by simp]
    exact (map_ne_zero_iff _ (algebraMap ℚ K).injective).2 two_ne_zero⟩
  obtain ⟨ψ⟩ := QuaternionAlgebra.nonempty_algEquiv_matrix_of_ne_zero_of_not_isUnit haK hbK (φ₁ x) hx1 hx1u
  obtain ⟨φ₀, hφ₀1, -⟩ := QuaternionAlgebra.exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
    (R := ℚ) (S := K) (c₁ := a) (c₂ := (0 : ℚ)) (c₃ := b) (d₁ := algebraMap ℚ K a) (d₂ := (0 : K)) (d₃ := algebraMap ℚ K b)
    rfl (map_zero _) rfl ψ

  obtain ⟨h, hh⟩ := QuaternionAlgebra.IsMaximalOrder.exists_localBox_iff_generalLinearGroup_conj_mem_adicCompletionIntegers
    hΛ v φ₀ hφ₀1
  refine ⟨φ₀.trans (ASM21.MLS.conjEquiv h), ?_, ?_⟩
  · intro r
    rw [RingEquiv.trans_apply, ASM21.MLS.conjEquiv_apply, hφ₀1, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      Units.inv_mul]
  · intro y
    rw [hh y]
    simp only [RingEquiv.trans_apply, ASM21.MLS.conjEquiv_apply]

end S_QuaternionAlgebra_IsMaximalOrder_exists_ringEquiv_mem_localBox_iff_of_isIndefiniteRamifiedExactlyAt_of_prime
end P2MW
export P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_ringEquiv_mem_localBox_iff_of_isIndefiniteRamifiedExactlyAt_of_prime (solution)
