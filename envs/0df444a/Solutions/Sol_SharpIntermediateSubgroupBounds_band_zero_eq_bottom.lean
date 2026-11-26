-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.band_zero_eq_bottom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:51:54.815752+00:00
-- url     : https://prove2.me/submissions/d4e241af-cfab-4604-89c5-bdd5b334e75a

import Definitions.Def_SharpIntermediateSubgroupBounds_Escape
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring
import Definitions.Def_SharpIntermediateSubgroupBounds_Packing
import Theorems.Thm_SharpIntermediateSubgroupBounds_BranchingTree_branchProduct_zero
import Theorems.Thm_SharpIntermediateSubgroupBounds_escapeBranchProduct_cons
attribute [local simp] SharpIntermediateSubgroupBounds.BranchingTree.branchProduct_zero
attribute [local simp] SharpIntermediateSubgroupBounds.escapeBranchProduct_cons



set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators
noncomputable section
universe u
variable {G : Type u} [Group G] [Fintype G]
attribute [local instance] SharpIntermediateSubgroupBounds.packingSubgroupDecidableEq
attribute [local instance] SharpIntermediateSubgroupBounds.subgroupFinite
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {H : Subgroup G} {q : ℕ}
    (hq : 1 < q) (hqp : q ≤ H.index.minFac) (K : band H q 0) :
    K.1 = H := by
  by_contra hne
  have hlt : H < K.1 := lt_of_le_of_ne K.2.1 (Ne.symm hne)
  have hmin : H.index.minFac ≤ H.relIndex K.1 :=
    minFac_le_relIndex_of_lt (le_refl H) hlt
  have hupper : H.relIndex K.1 < q := by
    simpa using K.2.2.2
  omega
end SharpIntermediateSubgroupBounds
