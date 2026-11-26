-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.intermediateSubgroups_card_eq_Ici
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:59:43.084844+00:00
-- url     : https://prove2.me/submissions/1171c7ad-7ff4-47c9-b0f9-1df8e5dfc6d3

import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Order.Atoms
import Mathlib.GroupTheory.GroupAction.Quotient
import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_PrimePower

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Pointwise
noncomputable section
variable {G : Type*} [Group G] [Fintype G]
attribute [local instance] SharpIntermediateSubgroupBounds.subgroupCarrierFintype
attribute [local instance] SharpIntermediateSubgroupBounds.subgroupIntervalFintype
attribute [local instance] SharpIntermediateSubgroupBounds.coatomFiberFintype
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution (H : Subgroup G) :
    (intermediateSubgroups H).card = Fintype.card (Set.Ici H) := by
  classical
  let e : ↑(intermediateSubgroups H) ≃ Set.Ici H :=
    { toFun := fun K ↦ ⟨K.1, mem_intermediateSubgroups.mp K.2⟩
      invFun := fun K ↦ ⟨K.1, mem_intermediateSubgroups.mpr K.2⟩
      left_inv := by intro K; rfl
      right_inv := by intro K; rfl }
  rw [← Fintype.card_coe]
  exact Fintype.card_congr e
end SharpIntermediateSubgroupBounds
