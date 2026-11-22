-- Prove2me | solution 1 for P2M_ArithmeticTriangleRemovalInVectorSpaces_IsBalanced_comm___3c74011adbe1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:14:32.61988+00:00
-- url     : https://prove2.me/submissions/3ce23140-1e0f-4c39-905d-b33c77c121b6

module
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Uniform
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Decomposition

set_option autoImplicit true
@[expose] public section
public section
open Finset Function
open ArithmeticTriangleRemovalInVectorSpaces
variable {N : ℕ} {w w₁ w₂ w₃ σ σ₁ σ₂ σ₃ : ℕ → ℝ} {μ μ₁ μ₂ μ₃ p : ℝ}
namespace ArithmeticTriangleRemovalInVectorSpaces
namespace IsBalanced
theorem _root_.solution (hb : IsBalanced N w₁ w₂ w₃) : IsBalanced N w₃ w₂ w₁ := by
  obtain ⟨hw₁, hw₂, hw₃, hm₂, hm₃, hmom⟩ := hb
  refine ⟨hw₃, hw₂, hw₁, hm₂.trans hm₃.symm, hm₃.symm, ?_⟩
  rw [hm₃]
  linarith
end IsBalanced
end ArithmeticTriangleRemovalInVectorSpaces
