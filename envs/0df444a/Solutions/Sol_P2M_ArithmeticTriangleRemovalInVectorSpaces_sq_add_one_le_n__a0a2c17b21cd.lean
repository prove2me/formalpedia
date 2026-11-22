-- Prove2me | solution 1 for P2M_ArithmeticTriangleRemovalInVectorSpaces_sq_add_one_le_n__a0a2c17b21cd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:11:13.028868+00:00
-- url     : https://prove2.me/submissions/72f3408f-ba77-421d-83e8-108a15459fca

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
theorem _root_.solution (p : ℕ) (η : ℝ) : (2 ^ (p + 3) * p ^ 10 / η) ^ 2 + 1 ≤ n₀ p η := by
  rw [n₀]
  push_cast
  gcongr ?_ + 1
  exact (Nat.le_ceil _).trans (le_add_of_nonneg_right (by positivity))
end ArithmeticTriangleRemovalInVectorSpaces
