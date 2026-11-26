-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.band_zero_card_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:03:08.306894+00:00
-- url     : https://prove2.me/submissions/9402cc69-b149-4c37-94b4-702ee19cb7d9

import Definitions.Def_SharpIntermediateSubgroupBounds_Escape
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring
import Definitions.Def_SharpIntermediateSubgroupBounds_Packing
import Theorems.Thm_SharpIntermediateSubgroupBounds_band_zero_subsingleton
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
    (hq : 1 < q) (hqp : q ≤ H.index.minFac) :
    Nat.card (band H q 0) = 1 := by
  let b : band H q 0 := ⟨H, le_rfl, by simp, by simpa using hq⟩
  let e : band H q 0 ≃ PUnit.{u + 1} :=
    { toFun := fun _ => PUnit.unit
      invFun := fun _ => b
      left_inv := fun K => (band_zero_subsingleton hq hqp K b).symm
      right_inv := by intro z; cases z; rfl }
  rw [Nat.card_congr e]
  simp
end SharpIntermediateSubgroupBounds
