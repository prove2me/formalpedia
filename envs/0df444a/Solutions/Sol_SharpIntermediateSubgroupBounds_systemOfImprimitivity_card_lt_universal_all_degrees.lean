-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.systemOfImprimitivity_card_lt_universal_all_degrees
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:08:51.605121+00:00
-- url     : https://prove2.me/submissions/b9070914-704c-4a62-817b-f60f6da4b759

import Mathlib.GroupTheory.GroupAction.Blocks
import Definitions.Def_SharpIntermediateSubgroupBounds_GroupMain
import Definitions.Def_SharpIntermediateSubgroupBounds_Blocks
import Theorems.Thm_SharpIntermediateSubgroupBounds_systemOfImprimitivity_card_eq_interval_card
import Theorems.Thm_SharpIntermediateSubgroupBounds_systemOfImprimitivity_card_lt_universal
import Theorems.Thm_SharpIntermediateSubgroupBounds_BranchingTree_branchProduct_zero
import Theorems.Thm_SharpIntermediateSubgroupBounds_escapeBranchProduct_cons
import Theorems.Thm_SharpIntermediateSubgroupBounds_natFloor_indexLog
import Theorems.Thm_SharpIntermediateSubgroupBounds_sharpConstant_two_decimal_enclosure
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
theorem _root_.solution (a : X) :
    (Fintype.card (SystemOfImprimitivity G X) : ℝ) <
      sharpConstant 2 *
        (Nat.card X : ℝ) ^ (indexLog 2 (Nat.card X) / 4) := by
  by_cases hX : 1 < Nat.card X
  · exact systemOfImprimitivity_card_lt_universal G X a hX
  · letI : Nonempty X := ⟨a⟩
    have hXone : Nat.card X = 1 := by
      have hXpos : 0 < Nat.card X := Nat.card_pos
      omega
    have hindex : (MulAction.stabilizer G a).index = 1 := by
      rw [MulAction.index_stabilizer_of_transitive G a, hXone]
    have hstab : MulAction.stabilizer G a = ⊤ :=
      Subgroup.index_eq_one.mp hindex
    have hcard : Fintype.card (SystemOfImprimitivity G X) = 1 := by
      rw [systemOfImprimitivity_card_eq_interval_card G X a, hstab]
      simp
    have hc : (1 : ℝ) < sharpConstant 2 := by
      have hc' := sharpConstant_two_decimal_enclosure.1
      norm_num at hc' ⊢
      linarith
    rw [hcard, hXone]
    norm_num [indexLog]
    exact hc
end SharpIntermediateSubgroupBounds
