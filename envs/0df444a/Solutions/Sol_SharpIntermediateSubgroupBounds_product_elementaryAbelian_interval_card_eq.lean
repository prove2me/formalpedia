-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.product_elementaryAbelian_interval_card_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:58:23.640012+00:00
-- url     : https://prove2.me/submissions/1b2f18c5-57b4-4546-bcc9-23a88e474234

import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Order.Atoms
import Mathlib.GroupTheory.GroupAction.Quotient
import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_PrimePower
import Theorems.Thm_SharpIntermediateSubgroupBounds_normal_elementaryAbelian_quotient_interval_card_eq

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
theorem _root_.solution
    (H₀ : Type u) [Group H₀] [Fintype H₀]
    (p a : ℕ) [Fact p.Prime] :
    Fintype.card
        (Set.Ici ((⊤ : Subgroup H₀).prod
          (⊥ : Subgroup (Multiplicative (Fin a → ZMod p))))) =
      totalQBinom p a := by
  exact normal_elementaryAbelian_quotient_interval_card_eq
    ((⊤ : Subgroup H₀).prod
      (⊥ : Subgroup (Multiplicative (Fin a → ZMod p))))
    (productTopBotQuotientEquiv H₀
      (Multiplicative (Fin a → ZMod p)))
end SharpIntermediateSubgroupBounds
