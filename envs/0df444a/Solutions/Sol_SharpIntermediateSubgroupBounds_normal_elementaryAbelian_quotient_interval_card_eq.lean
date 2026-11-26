-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.normal_elementaryAbelian_quotient_interval_card_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:57:45.760445+00:00
-- url     : https://prove2.me/submissions/b29b6665-6042-4919-a6c4-b995a3a740ac

import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Order.Atoms
import Mathlib.GroupTheory.GroupAction.Quotient
import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_PrimePower
import Theorems.Thm_SharpIntermediateSubgroupBounds_card_all_subspaces_fin_zmod


set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Pointwise
noncomputable section
variable {G : Type*} [Group G] [Fintype G]
attribute [local instance] SharpIntermediateSubgroupBounds.subgroupCarrierFintype
attribute [local instance] SharpIntermediateSubgroupBounds.subgroupIntervalFintype
attribute [local instance] SharpIntermediateSubgroupBounds.coatomFiberFintype
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {p a : ℕ}
    (H : Subgroup G) [H.Normal]
    (e : (G ⧸ H) ≃* Multiplicative (Fin a → ZMod p)) [Fact p.Prime] :
    Fintype.card (Set.Ici H) = totalQBinom p a := by
  classical
  calc
    Fintype.card (Set.Ici H) = Fintype.card (Subgroup (G ⧸ H)) :=
      Fintype.card_congr (QuotientGroup.comapMk'OrderIso H).toEquiv.symm
    _ = Fintype.card (Subgroup (Multiplicative (Fin a → ZMod p))) :=
      Fintype.card_congr e.mapSubgroup.toEquiv
    _ = Fintype.card (AddSubgroup (Fin a → ZMod p)) :=
      Fintype.card_congr AddSubgroup.toSubgroup.toEquiv.symm
    _ = Fintype.card (Submodule (ZMod p) (Fin a → ZMod p)) :=
      Fintype.card_congr (AddSubgroup.toZModSubmodule p).toEquiv
    _ = totalQBinom p a := by
      rw [Fintype.card_eq_nat_card]
      exact card_all_subspaces_fin_zmod p a
end SharpIntermediateSubgroupBounds
