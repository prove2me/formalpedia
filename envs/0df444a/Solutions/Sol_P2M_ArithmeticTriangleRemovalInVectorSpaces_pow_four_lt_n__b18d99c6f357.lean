-- Prove2me | solution 1 for P2M_ArithmeticTriangleRemovalInVectorSpaces_pow_four_lt_n__b18d99c6f357
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:13:40.046024+00:00
-- url     : https://prove2.me/submissions/48004047-32ef-4897-9f3e-bd0dc4dc898c

module
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Exponent

set_option autoImplicit true
@[expose] public section
public section
open Finset Filter Topology
open ArithmeticTriangleRemovalInVectorSpaces
namespace ArithmeticTriangleRemovalInVectorSpaces
theorem _root_.solution (p : ℕ) (η : ℝ) : p ^ 4 < n₀ p η := by
  grind [n₀]
end ArithmeticTriangleRemovalInVectorSpaces
