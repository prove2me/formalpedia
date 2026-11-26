-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.systemOfImprimitivity_card_lt_universal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:07:25.384257+00:00
-- url     : https://prove2.me/submissions/43f99a3b-e5d8-4bbe-a616-a0d47e9ff40c

import Mathlib.GroupTheory.GroupAction.Blocks
import Definitions.Def_SharpIntermediateSubgroupBounds_GroupMain
import Definitions.Def_SharpIntermediateSubgroupBounds_Blocks
import Theorems.Thm_SharpIntermediateSubgroupBounds_blockMem_card_lt_universal

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
theorem _root_.solution (a : X)
    (hX : 1 < Nat.card X) :
    (Fintype.card (SystemOfImprimitivity G X) : ℝ) <
      sharpConstant 2 *
        (Nat.card X : ℝ) ^ (indexLog 2 (Nat.card X) / 4) := by
  have hpointed := blockMem_card_lt_universal G X a hX
  rw [Fintype.card_congr (pointedBlock_systemOfImprimitivityEquiv G X a)] at hpointed
  exact hpointed
end SharpIntermediateSubgroupBounds
