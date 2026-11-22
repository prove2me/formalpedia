-- Prove2me | solution 1 for P2M_ArithmeticTriangleRemovalInVectorSpaces_IsBalanced_comm___927a6ae1263a
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:14:31.914187+00:00
-- url     : https://prove2.me/submissions/cf85faf2-29cf-454b-8905-eb93ef342763

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
theorem _root_.solution (hb : IsBalanced N w₁ w₂ w₃) : IsBalanced N w₁ w₃ w₂ := by
  obtain ⟨hw₁, hw₂, hw₃, hm₂, hm₃, hmom⟩ := hb
  exact ⟨hw₁, hw₃, hw₂, hm₃, hm₂, by linarith⟩
end IsBalanced
end ArithmeticTriangleRemovalInVectorSpaces
