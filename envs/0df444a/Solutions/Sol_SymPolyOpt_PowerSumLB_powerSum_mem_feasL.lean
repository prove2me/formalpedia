-- Prove2me | solution 1 for SymPolyOpt.PowerSumLB.powerSum_mem_feasL
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T03:27:37.816979+00:00
-- url     : https://prove2.me/submissions/38c42d2f-99f6-403d-a56a-1e3fd8dff8fc

import Mathlib
import Definitions.Def_SymPolyOpt_PowerSumLB_Setting

set_option autoImplicit false
open SymPolyOpt.PowerSumLB

theorem solution (n m : ℕ) (γ : ℕ → ℝ) :
    ∀ x ∈ feasP n m γ, powerSum x ∈ feasL n m γ := by
  intro x hx
  refine ⟨?_, ?_, ?_⟩
  · set A : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun k i => x k ^ (i : ℕ) with hA
    have h := Matrix.posSemidef_conjTranspose_mul_self A
    convert h using 1
    ext i j
    simp [hankel, powerSum, hA, Matrix.mul_apply, pow_add]
  · simp [powerSum]
  · intro j h1 h2
    exact hx j h1 h2
