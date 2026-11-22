-- Prove2me | solution 1 for P2M_ArithmeticTriangleRemovalInVectorSpaces_Compatible_comm___bf003541382f
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:12:28.704203+00:00
-- url     : https://prove2.me/submissions/73e15ba7-85bf-4b9f-a7e7-927958c469df

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Basic
public import Theorems.Thm_P2M_ArithmeticTriangleRemovalInVectorSpaces_Compatible_comm___20106223d85b
public import Theorems.Thm_P2M_ArithmeticTriangleRemovalInVectorSpaces_Compatible_comm___c955cfa1f590

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ArithmeticTriangleRemovalInVectorSpaces
variable {N : ℕ} {J J' : ℕ × ℕ × ℕ → ℝ} {g : ℕ × ℕ × ℕ → ℕ} {π₁ π₂ π₃ π₁' π₂' π₃' : ℕ → ℝ}
namespace ArithmeticTriangleRemovalInVectorSpaces
namespace Compatible
theorem _root_.solution (h : Compatible N π₁ π₂ π₃) : Compatible N π₃ π₂ π₁ :=
  h.comm₁₂.comm₂₃.comm₁₂
end Compatible
end ArithmeticTriangleRemovalInVectorSpaces
