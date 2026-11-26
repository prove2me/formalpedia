-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.elementarySubgroup_finrank_eq_sub_of_index
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:59:44.026256+00:00
-- url     : https://prove2.me/submissions/634c154f-7041-48fa-ade7-0c5013f997be

import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Order.Atoms
import Mathlib.GroupTheory.GroupAction.Quotient
import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_PrimePower
import Theorems.Thm_SharpIntermediateSubgroupBounds_card_elementarySubgroup

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Pointwise
noncomputable section
variable {G : Type*} [Group G] [Fintype G]
attribute [local instance] SharpIntermediateSubgroupBounds.subgroupCarrierFintype
attribute [local instance] SharpIntermediateSubgroupBounds.subgroupIntervalFintype
attribute [local instance] SharpIntermediateSubgroupBounds.coatomFiberFintype
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {p a k : ℕ} [Fact p.Prime]
    (hk : k ≤ a) (Q : Subgroup (Multiplicative (Fin a → ZMod p)))
    (hindex : Q.index = p ^ k) :
    Module.finrank (ZMod p) (elementarySubgroupSubmoduleIso p a Q) = a - k := by
  have hcardQ := card_elementarySubgroup Q
  have hcardAmbient : Nat.card (Multiplicative (Fin a → ZMod p)) = p ^ a := by
    rw [Nat.card_eq_fintype_card]
    simpa using (Module.card_eq_pow_finrank (K := ZMod p)
      (V := Fin a → ZMod p))
  have htower := Q.card_mul_index
  have hpowequal :
      p ^ (Module.finrank (ZMod p) (elementarySubgroupSubmoduleIso p a Q) + k) =
        p ^ a := by
    rw [pow_add, ← hcardQ, ← hindex, htower, hcardAmbient]
  have hadd := Nat.pow_right_injective ((Fact.out : p.Prime).two_le) hpowequal
  omega
end SharpIntermediateSubgroupBounds
