-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.product_elementaryAbelian_index_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:00:00.405672+00:00
-- url     : https://prove2.me/submissions/3dea50e7-23e5-4a6e-8f95-b695eb3e1ab6

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
universe u v
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution
    (H₀ : Type u) [Group H₀] [Fintype H₀]
    (p a : ℕ) [Fact p.Prime] :
    ((⊤ : Subgroup H₀).prod
      (⊥ : Subgroup (Multiplicative (Fin a → ZMod p)))).index = p ^ a := by
  rw [Subgroup.index_prod]
  simp only [Subgroup.index_top, one_mul, Subgroup.index_bot]
  rw [Nat.card_eq_fintype_card]
  simpa using (Module.card_eq_pow_finrank (K := ZMod p)
    (V := Fin a → ZMod p))
end SharpIntermediateSubgroupBounds
