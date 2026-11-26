-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.product_elementaryAbelian_even_family
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:04:41.054535+00:00
-- url     : https://prove2.me/submissions/bdb9e38e-d0ba-42c3-b702-b30dc9249e1c

import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Order.Atoms
import Mathlib.GroupTheory.GroupAction.Quotient
import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_PrimePower
import Theorems.Thm_SharpIntermediateSubgroupBounds_product_elementaryAbelian_family

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
      (⊥ : Subgroup (Multiplicative (Fin (2 * a) → ZMod p)))).index =
        p ^ (2 * a) ∧
      Fintype.card
          (Set.Ici ((⊤ : Subgroup H₀).prod
            (⊥ : Subgroup (Multiplicative (Fin (2 * a) → ZMod p))))) =
        totalQBinom p (2 * a) :=
  product_elementaryAbelian_family H₀ p (2 * a)
end SharpIntermediateSubgroupBounds
