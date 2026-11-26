-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.escapeTuple_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:51:24.930496+00:00
-- url     : https://prove2.me/submissions/aa842f75-02cd-4d36-80d7-6f9dbabf099d

import Definitions.Def_SharpIntermediateSubgroupBounds_Tree
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring
import Definitions.Def_SharpIntermediateSubgroupBounds_Escape
import Theorems.Thm_SharpIntermediateSubgroupBounds_BranchingTree_branchProduct_zero
attribute [local simp] SharpIntermediateSubgroupBounds.BranchingTree.branchProduct_zero



set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators
noncomputable section
universe u
variable {G : Type u} [Group G] [Fintype G]
attribute [local instance] SharpIntermediateSubgroupBounds.subgroupDecidableEq
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution (K : Subgroup G) {r : ℕ} {s : EscapeState K} :
    Function.Injective (escapeTuple K : EscapePath K r s → Fin r → G) := by
  induction r generalizing s with
  | zero =>
      intro x y _
      cases x
      cases y
      rfl
  | succ r ih =>
      rintro ⟨x, z⟩ ⟨y, w⟩ h
      have hxy : x = y := by
        apply Subtype.ext
        apply Subtype.ext
        simpa [escapeTuple] using congrFun h 0
      subst y
      have hzw : escapeTuple K z = escapeTuple K w := by
        funext i
        simpa [escapeTuple] using congrFun h i.succ
      have := ih (s := escapeNext K s x) hzw
      subst w
      rfl
end SharpIntermediateSubgroupBounds
