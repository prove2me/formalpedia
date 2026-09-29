-- Prove2me | solution 1 for QuaternionAlgebra.IsOrder.surjective_and_apply_eq_zero_iff_of_linearMap_matrix_zmod
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/e6e1bd0f-ea38-508d-a7c3-9b89ff5c0c0b

import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsOrder_surjective_and_apply_eq_zero_iff_of_linearMap_matrix_zmod

set_option autoImplicit false

open scoped Quaternion

namespace MatModNRigid

open Matrix

variable {N : ℕ} [NeZero N]

abbrev E (i j : Fin 2) : Matrix (Fin 2) (Fin 2) (ZMod N) := Matrix.single i j 1

theorem single_mul_mul_single (X : Matrix (Fin 2) (Fin 2) (ZMod N)) (p i j q : Fin 2) :
    E p i * X * E j q = X i j • E p q := by
  ext r s
  simp only [Matrix.mul_apply, Matrix.smul_apply, E, Matrix.single, Matrix.of_apply, Fin.sum_univ_two, smul_eq_mul]
  fin_cases p <;> fin_cases q <;> fin_cases r <;> fin_cases s <;> fin_cases i <;> fin_cases j <;> simp

theorem E_sum : E 0 0 + E 1 1 = (1 : Matrix (Fin 2) (Fin 2) (ZMod N)) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [E, Matrix.single, Matrix.one_apply]

theorem injective_of_ringHom (θ : Matrix (Fin 2) (Fin 2) (ZMod N) →+* Matrix (Fin 2) (Fin 2) (ZMod N)) :
    Function.Injective θ := by
  rw [injective_iff_map_eq_zero]
  intro X hX
  have hsmul : ∀ (r : ZMod N) (Y : Matrix (Fin 2) (Fin 2) (ZMod N)), θ (r • Y) = r • θ Y := by
    intro r Y
    rw [← ZMod.natCast_zmod_val r, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, map_nsmul]
  have hent : ∀ i j p q : Fin 2, X i j • θ (E p q) = 0 := by
    intro i j p q
    rw [← hsmul, ← single_mul_mul_single X p i j q, map_mul, map_mul, hX, mul_zero, zero_mul]
  ext i j
  have h : X i j • θ 1 = 0 := by
    rw [← E_sum, map_add, smul_add, hent, hent, add_zero]
  rw [map_one] at h
  have := congrFun (congrFun h 0) 0
  simpa using this

end MatModNRigid

open MatModNRigid in
theorem solution
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsOrder Λ) (N : ℕ) [NeZero N]
    (φ ψ : ↥Λ →ₗ[ℤ] Matrix (Fin 2) (Fin 2) (ZMod N))
    (hφ1 : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, φ ⟨1, h⟩ = 1)
    (hφmul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      φ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = φ x * φ y)
    (hφsurj : Function.Surjective φ)
    (hφker : ∀ x : ↥Λ, φ x = 0 ↔ ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (N : ℚ) • (y : ℍ[ℚ, a, b]))
    (hψ1 : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, ψ ⟨1, h⟩ = 1)
    (hψmul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      ψ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = ψ x * ψ y) :
    Function.Surjective ψ ∧
      ∀ x : ↥Λ, ψ x = 0 ↔ ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (N : ℚ) • (y : ℍ[ℚ, a, b]) := by
  classical

  have hψN : ∀ y : ↥Λ, ψ ((N : ℤ) • y) = 0 := by
    intro y
    rw [map_zsmul, zsmul_eq_mul, Int.cast_natCast]
    ext i j; simp [Matrix.mul_apply, ZMod.natCast_self]
  have hwd : ∀ m m' : ↥Λ, φ m = φ m' → ψ m = ψ m' := by
    intro m m' h
    have h0 : φ (m - m') = 0 := by rw [map_sub, h, sub_self]
    obtain ⟨y, hy⟩ := (hφker _).mp h0
    have : m - m' = (N : ℤ) • y := by
      apply Subtype.ext
      rw [hy, Submodule.coe_smul_of_tower, ← Int.cast_smul_eq_zsmul ℚ, Int.cast_natCast]
    have := congrArg ψ this
    rw [map_sub, hψN] at this
    exact sub_eq_zero.mp this
  let s : Matrix (Fin 2) (Fin 2) (ZMod N) → ↥Λ := Function.surjInv hφsurj
  have hs : ∀ A, φ (s A) = A := Function.surjInv_eq hφsurj
  have hψs : ∀ m : ↥Λ, ψ (s (φ m)) = ψ m := fun m => hwd _ _ (hs (φ m))

  let θ : Matrix (Fin 2) (Fin 2) (ZMod N) →+* Matrix (Fin 2) (Fin 2) (ZMod N) :=
    { toFun := fun A => ψ (s A)
      map_one' := by
        have : φ (s 1) = φ ⟨1, hΛ.one_mem⟩ := by rw [hs, hφ1]
        show ψ (s 1) = 1
        rw [hwd _ _ this, hψ1]
      map_mul' := fun A B => by
        have hmem : ((s A : ℍ[ℚ, a, b]) * (s B : ℍ[ℚ, a, b])) ∈ Λ := hΛ.mul_mem (s A).2 (s B).2
        have : φ (s (A * B)) = φ ⟨_, hmem⟩ := by rw [hs, hφmul, hs, hs]
        show ψ (s (A * B)) = ψ (s A) * ψ (s B)
        rw [hwd _ _ this, hψmul]
      map_zero' := by
        have : φ (s 0) = φ 0 := by rw [hs, map_zero]
        show ψ (s 0) = 0
        rw [hwd _ _ this, map_zero]
      map_add' := fun A B => by
        have : φ (s (A + B)) = φ (s A + s B) := by rw [hs, map_add, hs, hs]
        show ψ (s (A + B)) = ψ (s A) + ψ (s B)
        rw [hwd _ _ this, map_add] }
  have hθ : ∀ A, θ A = ψ (s A) := fun _ => rfl
  have hinj : Function.Injective θ := injective_of_ringHom θ
  have hbij : Function.Bijective θ := Finite.injective_iff_bijective.mp hinj
  refine ⟨?_, ?_⟩
  · intro m
    obtain ⟨A, hA⟩ := hbij.2 m
    exact ⟨s A, hA⟩
  · intro x
    rw [← hφker x, ← hψs x, ← hθ, map_eq_zero_iff θ hinj]

end S_QuaternionAlgebra_IsOrder_surjective_and_apply_eq_zero_iff_of_linearMap_matrix_zmod
end P2MW
export P2MW.S_QuaternionAlgebra_IsOrder_surjective_and_apply_eq_zero_iff_of_linearMap_matrix_zmod (solution)
