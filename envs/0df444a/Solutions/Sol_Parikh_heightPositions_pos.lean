-- Prove2me | solution 1 for Parikh.heightPositions_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:49:31.013526+00:00
-- url     : https://prove2.me/submissions/c81f4041-3673-4478-8a3b-50df43ca70a8

module
public import Definitions.Def_LeanPool_Parikh_GrammarTrees
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Definitions.Def_LeanPool_Parikh_BoundedFamilySupport
public import Theorems.Thm_Parikh_heightPositions_zero
public import Theorems.Thm_Parikh_heightPositions_succ

set_option autoImplicit true
@[expose] public section
public section
open Parikh
namespace Parikh
theorem _root_.solution (b H : ℕ) : 1 ≤ heightPositions b H := by
  cases H with
  | zero => simp [heightPositions_zero]
  | succ H => rw [heightPositions_succ]; omega
end Parikh
