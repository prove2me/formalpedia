-- Prove2me | solution 1 for SuttonTD.Convergence.theorem_A_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T04:32:39.496812+00:00
-- url     : https://prove2.me/submissions/b00396e7-002f-40c4-a014-b54588f9fb56

import Mathlib

set_option autoImplicit false

open Matrix in
theorem solution {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m n ℝ)
    (hA : LinearIndependent ℝ (fun j : n => fun i : m => A i j)) :
    IsUnit (Aᵀ * A) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  have key : ∀ v : n → ℝ, (Aᵀ * A) *ᵥ v = 0 → v = 0 := by
    intro v hv
    have h1 : (A *ᵥ v) ⬝ᵥ (A *ᵥ v) = 0 := by
      have : v ⬝ᵥ ((Aᵀ * A) *ᵥ v) = 0 := by rw [hv, dotProduct_zero]
      rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose] at this
      exact this
    have h2 : A *ᵥ v = 0 := dotProduct_self_eq_zero.mp h1
    rw [Fintype.linearIndependent_iff] at hA
    funext j
    apply hA v
    funext i
    have := congrFun h2 i
    simpa [Matrix.mulVec, dotProduct, mul_comm] using this
  intro x y hxy
  have := key (x - y) (by rw [Matrix.mulVec_sub, hxy, sub_self])
  exact sub_eq_zero.mp this

#print axioms solution
