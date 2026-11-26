-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.primePower_layer_bound_optimal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:04:45.194943+00:00
-- url     : https://prove2.me/submissions/638cdcd7-b1b4-491a-8288-7ba040de01ca

import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Order.Atoms
import Mathlib.GroupTheory.GroupAction.Quotient
import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_PrimePower
import Theorems.Thm_SharpIntermediateSubgroupBounds_primePowerLayer_card_le
import Theorems.Thm_SharpIntermediateSubgroupBounds_elementaryAbelian_primePowerLayer_card_eq_qBinom

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
theorem _root_.solution (p a k : ℕ) [Fact p.Prime]
    (hk : k ≤ a) :
    (∀ {G : Type*} [Group G] [Fintype G] (H : Subgroup G),
      H.index = p ^ a →
        (primePowerLayer p k H ⊤).card ≤ qBinom p a k) ∧
      (primePowerLayer p k
        (⊥ : Subgroup (Multiplicative (Fin a → ZMod p))) ⊤).card =
        qBinom p a k := by
  constructor
  · intro G _ _ H hindex
    exact primePowerLayer_card_le Fact.out H hindex
  · exact elementaryAbelian_primePowerLayer_card_eq_qBinom p a k hk
end SharpIntermediateSubgroupBounds
