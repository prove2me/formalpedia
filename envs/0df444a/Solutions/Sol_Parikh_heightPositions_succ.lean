-- Prove2me | solution 1 for Parikh.heightPositions_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:48:44.790476+00:00
-- url     : https://prove2.me/submissions/2a7cd84f-67dd-42bb-982f-1fcbfac94b5e

module
public import Definitions.Def_LeanPool_Parikh_GrammarTrees
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Definitions.Def_LeanPool_Parikh_BoundedFamilySupport

set_option autoImplicit true
@[expose] public section
public section
open Parikh
namespace Parikh
theorem _root_.solution (b H : ℕ) :
    heightPositions b (H + 1) = 1 + b * heightPositions b H := by
  unfold heightPositions
  rw [Finset.sum_range_succ']
  simp only [pow_succ', pow_zero]
  rw [Finset.mul_sum]
  omega
end Parikh
