-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.elementaryAbelian_interval_card_eq_totalQBinom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:57:44.15109+00:00
-- url     : https://prove2.me/submissions/e85d8732-413e-4b93-b2aa-5f106b90220a

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
theorem _root_.solution (p a : ℕ) [Fact p.Prime] :
    Fintype.card
        (Set.Ici (⊥ : Subgroup (Multiplicative (Fin a → ZMod p)))) = totalQBinom p a := by
  classical
  let forgetBottom :
      Set.Ici (⊥ : Subgroup (Multiplicative (Fin a → ZMod p))) ≃
        Subgroup (Multiplicative (Fin a → ZMod p)) :=
    { toFun := Subtype.val
      invFun := fun K ↦
        ⟨K, (show (⊥ : Subgroup (Multiplicative (Fin a → ZMod p))) ≤ K from bot_le)⟩
      left_inv := by intro K; rfl
      right_inv := by intro K; rfl }
  calc
    Fintype.card (Set.Ici (⊥ : Subgroup (Multiplicative (Fin a → ZMod p)))) =
        Fintype.card (Subgroup (Multiplicative (Fin a → ZMod p))) :=
      Fintype.card_congr forgetBottom
    _ = Fintype.card (AddSubgroup (Fin a → ZMod p)) :=
      Fintype.card_congr AddSubgroup.toSubgroup.toEquiv.symm
    _ = Fintype.card (Submodule (ZMod p) (Fin a → ZMod p)) :=
      Fintype.card_congr (AddSubgroup.toZModSubmodule p).toEquiv
    _ = totalQBinom p a := by
      rw [Fintype.card_eq_nat_card]
      exact card_all_subspaces_fin_zmod p a
end SharpIntermediateSubgroupBounds
