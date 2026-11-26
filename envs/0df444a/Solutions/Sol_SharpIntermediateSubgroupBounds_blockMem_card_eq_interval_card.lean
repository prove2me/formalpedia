-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.blockMem_card_eq_interval_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:02:04.772791+00:00
-- url     : https://prove2.me/submissions/7e45c389-b769-49cb-a7ce-017166796048

import Mathlib.GroupTheory.GroupAction.Blocks
import Definitions.Def_SharpIntermediateSubgroupBounds_GroupMain
import Definitions.Def_SharpIntermediateSubgroupBounds_Blocks

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
theorem _root_.solution (a : X) :
    Fintype.card (MulAction.BlockMem G a) =
      Fintype.card (Set.Ici (MulAction.stabilizer G a)) := by
  classical
  exact Fintype.card_congr (MulAction.block_stabilizerOrderIso G a).toEquiv
end SharpIntermediateSubgroupBounds
