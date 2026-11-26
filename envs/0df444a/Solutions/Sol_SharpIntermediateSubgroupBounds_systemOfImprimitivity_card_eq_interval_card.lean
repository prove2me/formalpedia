-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.systemOfImprimitivity_card_eq_interval_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:02:07.36763+00:00
-- url     : https://prove2.me/submissions/c4df706d-4701-47e0-a6a3-c3191525a404

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
    Fintype.card (SystemOfImprimitivity G X) =
      Fintype.card (Set.Ici (MulAction.stabilizer G a)) := by
  classical
  exact Fintype.card_congr
    ((pointedBlock_systemOfImprimitivityEquiv G X a).symm.trans
      (MulAction.block_stabilizerOrderIso G a).toEquiv)
end SharpIntermediateSubgroupBounds
