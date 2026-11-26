-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.product_elementaryAbelian_family
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:00:40.49594+00:00
-- url     : https://prove2.me/submissions/aaa8ea56-791e-41d0-ac34-4f89097aa7e1

import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Order.Atoms
import Mathlib.GroupTheory.GroupAction.Quotient
import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_PrimePower
import Theorems.Thm_SharpIntermediateSubgroupBounds_product_elementaryAbelian_interval_card_eq
import Theorems.Thm_SharpIntermediateSubgroupBounds_product_elementaryAbelian_index_eq

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
    ((⊤ : Subgroup H₀).prod
      (⊥ : Subgroup (Multiplicative (Fin a → ZMod p)))).index = p ^ a ∧
      Fintype.card
          (Set.Ici ((⊤ : Subgroup H₀).prod
            (⊥ : Subgroup (Multiplicative (Fin a → ZMod p))))) =
        totalQBinom p a :=
  ⟨product_elementaryAbelian_index_eq H₀ p a,
    product_elementaryAbelian_interval_card_eq H₀ p a⟩
end SharpIntermediateSubgroupBounds
