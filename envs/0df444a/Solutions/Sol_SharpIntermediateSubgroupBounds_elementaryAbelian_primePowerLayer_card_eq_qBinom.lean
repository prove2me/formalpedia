-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.elementaryAbelian_primePowerLayer_card_eq_qBinom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:00:22.550697+00:00
-- url     : https://prove2.me/submissions/6accab89-c9ab-4d54-ad11-f2b47ca1e881

import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Order.Atoms
import Mathlib.GroupTheory.GroupAction.Quotient
import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_PrimePower
import Theorems.Thm_SharpIntermediateSubgroupBounds_elementarySubgroup_finrank_eq_sub_of_index
import Theorems.Thm_SharpIntermediateSubgroupBounds_elementarySubgroup_index_eq_pow_of_finrank
import Theorems.Thm_SharpIntermediateSubgroupBounds_card_subspaces_fin_zmod
import Theorems.Thm_SharpIntermediateSubgroupBounds_qBinom_symm


set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Pointwise
noncomputable section
variable {G : Type*} [Group G] [Fintype G]
attribute [local instance] SharpIntermediateSubgroupBounds.subgroupCarrierFintype
attribute [local instance] SharpIntermediateSubgroupBounds.subgroupIntervalFintype
attribute [local instance] SharpIntermediateSubgroupBounds.coatomFiberFintype
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution (p a k : ℕ)
    [Fact p.Prime] (hk : k ≤ a) :
    (primePowerLayer p k
      (⊥ : Subgroup (Multiplicative (Fin a → ZMod p))) ⊤).card =
        qBinom p a k := by
  classical
  let E := elementarySubgroupSubmoduleIso p a
  let Target := {W : Submodule (ZMod p) (Fin a → ZMod p) //
    Module.finrank (ZMod p) W = a - k}
  let toTarget (Q : ↑(primePowerLayer p k
      (⊥ : Subgroup (Multiplicative (Fin a → ZMod p))) ⊤)) : Target := by
    refine ⟨E Q.1, ?_⟩
    have hQl := mem_primePowerLayer.mp Q.2
    apply elementarySubgroup_finrank_eq_sub_of_index hk Q.1
    rw [← Subgroup.relIndex_top_right]
    exact hQl.2.2
  let fromTarget (W : Target) : ↑(primePowerLayer p k
      (⊥ : Subgroup (Multiplicative (Fin a → ZMod p))) ⊤) := by
    refine ⟨E.symm W.1, mem_primePowerLayer.mpr ⟨bot_le, le_top, ?_⟩⟩
    rw [Subgroup.relIndex_top_right]
    apply elementarySubgroup_index_eq_pow_of_finrank hk
    change Module.finrank (ZMod p) (E (E.symm W.1)) = a - k
    rw [E.apply_symm_apply]
    exact W.2
  let e : ↑(primePowerLayer p k
      (⊥ : Subgroup (Multiplicative (Fin a → ZMod p))) ⊤) ≃ Target :=
    { toFun := toTarget
      invFun := fromTarget
      left_inv := by intro Q; apply Subtype.ext; exact E.symm_apply_apply Q.1
      right_inv := by intro W; apply Subtype.ext; exact E.apply_symm_apply W.1 }
  rw [← Fintype.card_coe]
  calc
    Fintype.card ↑(primePowerLayer p k
        (⊥ : Subgroup (Multiplicative (Fin a → ZMod p))) ⊤) =
      Fintype.card Target := Fintype.card_congr e
    _ = Nat.card Target := Fintype.card_eq_nat_card
    _ = qBinom p a (a - k) :=
      card_subspaces_fin_zmod p a (a - k) (Nat.sub_le _ _)
    _ = qBinom p a k := (qBinom_symm (q := p) (n := a) (k := k)
      (Fact.out : p.Prime).two_le hk).symm
end SharpIntermediateSubgroupBounds
