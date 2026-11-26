-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.primePower_interval_bound_optimal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:02:49.007006+00:00
-- url     : https://prove2.me/submissions/555224e2-2999-4e48-9c57-182792f88d8f

import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Order.Atoms
import Mathlib.GroupTheory.GroupAction.Quotient
import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_PrimePower
import Theorems.Thm_SharpIntermediateSubgroupBounds_intermediate_interval_card_le_totalQBinom
import Theorems.Thm_SharpIntermediateSubgroupBounds_elementaryAbelian_interval_card_eq_totalQBinom

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Pointwise
noncomputable section
variable {G : Type*} [Group G] [Fintype G]
attribute [local instance] SharpIntermediateSubgroupBounds.subgroupCarrierFintype
attribute [local instance] SharpIntermediateSubgroupBounds.subgroupIntervalFintype
attribute [local instance] SharpIntermediateSubgroupBounds.coatomFiberFintype
universe u v
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution (p a : ℕ) [Fact p.Prime] :
    (∀ {G : Type*} [Group G] [Fintype G] (H : Subgroup G), H.index = p ^ a →
      Fintype.card (Set.Ici H) ≤ totalQBinom p a) ∧
    Fintype.card
        (Set.Ici (⊥ : Subgroup (Multiplicative (Fin a → ZMod p)))) = totalQBinom p a := by
  constructor
  · intro G _ _ H hindex
    exact intermediate_interval_card_le_totalQBinom Fact.out H hindex
  · exact elementaryAbelian_interval_card_eq_totalQBinom p a
end SharpIntermediateSubgroupBounds
