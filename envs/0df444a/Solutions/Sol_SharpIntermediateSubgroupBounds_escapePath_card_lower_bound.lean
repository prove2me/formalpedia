-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.escapePath_card_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:54:53.762811+00:00
-- url     : https://prove2.me/submissions/26121936-3d1c-4ec2-98d1-f526219ff1fa

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
import Theorems.Thm_SharpIntermediateSubgroupBounds_escape_path_full_gamma_bound
import Theorems.Thm_SharpIntermediateSubgroupBounds_BranchingTree_leaf_product_bound_sameUniverse


set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators
noncomputable section
universe u
variable {G : Type u} [Group G] [Fintype G]
attribute [local instance] SharpIntermediateSubgroupBounds.subgroupDecidableEq
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {H K : Subgroup G}
    (hn : 1 < H.index) (hHK : H ≤ K) (r : ℕ) :
    gammaQ H.index.minFac r * (Nat.card K : ℚ) ^ r ≤
      (Fintype.card (EscapePath K r ⟨H, hHK⟩) : ℚ) := by
  apply BranchingTree.leaf_product_bound_sameUniverse
    (Choice := fun s : EscapeState K => EscapeChoice K s)
    (next := fun s x => escapeNext K s x)
  intro z
  exact escape_path_full_gamma_bound hn hHK (le_refl H) z
end SharpIntermediateSubgroupBounds
