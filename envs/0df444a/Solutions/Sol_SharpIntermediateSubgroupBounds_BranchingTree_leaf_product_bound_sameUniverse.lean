-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.BranchingTree.leaf_product_bound_sameUniverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:51:37.045703+00:00
-- url     : https://prove2.me/submissions/a7f54c44-d2f3-4df7-9874-0547417debaf

import Definitions.Def_SharpIntermediateSubgroupBounds_Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Fintype.BigOperators
import Definitions.Def_SharpIntermediateSubgroupBounds_Tree
import Theorems.Thm_SharpIntermediateSubgroupBounds_BranchingTree_leaf_product_bound

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators
open SharpIntermediateSubgroupBounds.BranchingTree
universe u
variable {State : Type*}
variable (Choice : State → Type*) [∀ s, Fintype (Choice s)]
variable (next : ∀ s, Choice s → State)
namespace SharpIntermediateSubgroupBounds.BranchingTree
theorem _root_.solution {State : Type u}
    (Choice : State → Type u) [∀ s, Fintype (Choice s)]
    (next : ∀ s, Choice s → State) [∀ s, Nonempty (Choice s)]
    (r : ℕ) (s : State) (q : ℚ)
    (hq : ∀ z : Path Choice next r s,
      q ≤ (branchProduct Choice next z : ℚ)) :
    q ≤ (Fintype.card (Path Choice next r s) : ℚ) :=
  leaf_product_bound Choice next r s q hq
end SharpIntermediateSubgroupBounds.BranchingTree
