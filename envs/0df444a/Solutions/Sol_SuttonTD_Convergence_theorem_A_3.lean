-- Prove2me | solution 1 for SuttonTD.Convergence.theorem_A_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T18:31:42.715015+00:00
-- url     : https://prove2.me/submissions/cbad45a0-4b38-4bc9-873d-dc46ba09093f

import Mathlib
import Definitions.Def_SuttonTD_Convergence_IsPosDefReal

set_option autoImplicit false

open Matrix

open SuttonTD.Convergence in
theorem a90cec16_quad {n : Type*} [Fintype n] (A : Matrix n n ℝ) (y : n → ℝ) :
    y ⬝ᵥ ((A + Aᵀ) *ᵥ y) = 2 * (y ⬝ᵥ (A *ᵥ y)) := by
  have h : y ⬝ᵥ (Aᵀ *ᵥ y) = y ⬝ᵥ (A *ᵥ y) := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]
  rw [Matrix.add_mulVec, dotProduct_add, h]
  ring

open Matrix SuttonTD.Convergence in
theorem solution {n : Type*} [Fintype n] (A : Matrix n n ℝ) :
    IsPosDefReal A ↔ IsPosDefReal (A + Aᵀ) := by
  constructor
  · intro h y hy
    rw [a90cec16_quad]
    have := h y hy
    linarith
  · intro h y hy
    have := h y hy
    rw [a90cec16_quad] at this
    linarith
