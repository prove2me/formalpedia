-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.blockMem_card_lt_universal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:06:18.168396+00:00
-- url     : https://prove2.me/submissions/af16a5e8-2c5d-4615-9892-8b105456eb78

import Mathlib.GroupTheory.GroupAction.Blocks
import Definitions.Def_SharpIntermediateSubgroupBounds_GroupMain
import Definitions.Def_SharpIntermediateSubgroupBounds_Blocks
import Theorems.Thm_SharpIntermediateSubgroupBounds_blockMem_card_eq_interval_card
import Theorems.Thm_SharpIntermediateSubgroupBounds_BranchingTree_branchProduct_zero
import Theorems.Thm_SharpIntermediateSubgroupBounds_escapeBranchProduct_cons
import Theorems.Thm_SharpIntermediateSubgroupBounds_interval_card_lt_universal_rpow
import Theorems.Thm_SharpIntermediateSubgroupBounds_natFloor_indexLog
attribute [local simp] SharpIntermediateSubgroupBounds.BranchingTree.branchProduct_zero
attribute [local simp] SharpIntermediateSubgroupBounds.escapeBranchProduct_cons
attribute [local simp] SharpIntermediateSubgroupBounds.natFloor_indexLog



set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open MulAction
open scoped Pointwise
variable (G X : Type*) [Group G] [Fintype G] [Fintype X]
variable [MulAction G X] [MulAction.IsPretransitive G X]
attribute [local instance] SharpIntermediateSubgroupBounds.blockMemFintype
attribute [local instance] SharpIntermediateSubgroupBounds.blocksSubgroupFinite
attribute [local instance] SharpIntermediateSubgroupBounds.blocksIntervalFintype
attribute [local instance] SharpIntermediateSubgroupBounds.systemOfImprimitivityFintype
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution (a : X) (hX : 1 < Nat.card X) :
    (Fintype.card (MulAction.BlockMem G a) : ℝ) <
      sharpConstant 2 *
        (Nat.card X : ℝ) ^ (indexLog 2 (Nat.card X) / 4) := by
  have hindex : (MulAction.stabilizer G a).index = Nat.card X :=
    MulAction.index_stabilizer_of_transitive G a
  have hn : 1 < (MulAction.stabilizer G a).index := hindex.symm ▸ hX
  have hmain := interval_card_lt_universal_rpow
    (H := MulAction.stabilizer G a) hn
  rw [Nat.card_eq_fintype_card] at hmain
  change
    (Fintype.card (Set.Ici (MulAction.stabilizer G a)) : ℝ) <
      sharpConstant 2 *
        ((MulAction.stabilizer G a).index : ℝ) ^
          (indexLog 2 (MulAction.stabilizer G a).index / 4) at hmain
  rw [← blockMem_card_eq_interval_card G X a] at hmain
  simpa [hindex] using hmain
end SharpIntermediateSubgroupBounds
