-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.elementarySubgroup_index_eq_pow_of_finrank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:59:44.491553+00:00
-- url     : https://prove2.me/submissions/677165cc-a3c4-48eb-85de-4f82b688a1a2

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
    (hrank : Module.finrank (ZMod p) (elementarySubgroupSubmoduleIso p a Q) = a - k) :
    Q.index = p ^ k := by
  have hcardQ := card_elementarySubgroup Q
  have hcardAmbient : Nat.card (Multiplicative (Fin a → ZMod p)) = p ^ a := by
    rw [Nat.card_eq_fintype_card]
    simpa using (Module.card_eq_pow_finrank (K := ZMod p)
      (V := Fin a → ZMod p))
  apply Nat.mul_left_cancel (pow_pos (Fact.out : p.Prime).pos _)
  calc
    p ^ (a - k) * Q.index = Nat.card Q * Q.index := by rw [hcardQ, hrank]
    _ = Nat.card (Multiplicative (Fin a → ZMod p)) := Q.card_mul_index
    _ = p ^ a := hcardAmbient
    _ = p ^ (a - k) * p ^ k := by rw [← pow_add, Nat.sub_add_cancel hk]
end SharpIntermediateSubgroupBounds
