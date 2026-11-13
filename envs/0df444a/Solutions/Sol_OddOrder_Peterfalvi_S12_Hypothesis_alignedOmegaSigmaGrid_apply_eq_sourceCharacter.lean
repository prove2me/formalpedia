-- Prove2me | solution 1 for OddOrder.Peterfalvi.S12.Hypothesis.alignedOmegaSigmaGrid_apply_eq_sourceCharacter
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T17:17:56.812407+00:00
-- url     : https://prove2.me/submissions/0c2b128c-c370-4521-87ba-a1e7c2157c67

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S16_NonExistenceG/TGapNonorthogonality.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_TGapNonorthogonality

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/TGapNonorthogonality.lean =====
namespace OddOrder.Peterfalvi.S12

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

open scoped FiniteInduce in
set_option backward.isDefEq.respectTransparency false in
/-- On the type-P regular set, an aligned sigma-grid entry restores its
underlying multiplicative character.  This is the source-side counterpart of
S15's `tau3_apply_of_regular`. -/
theorem _root_.solution [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) (j : Fin hyp.w2) {v : G}
    (hv : v ∈ typePV M hyp.typeP) :
    hyp.alignedOmegaSigmaGrid hG hodd i j v =
      ((hyp.alignedOmegaSourceCharacter hG hodd i j
        ⟨v, hv.1⟩ : ℂˣ) : ℂ) := by
  have := hyp.finiteG
  classical
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  have : NeZero (Nat.card h.W1) :=
    ⟨by have := h.one_lt_card_W1; omega⟩
  have : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  let : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  have : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) :=
    ⟨Nat.card_pos.ne'⟩
  let χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ :=
    finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j)
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  have : NeZero (Nat.card ↥tic.W1) := ⟨Nat.card_pos.ne'⟩
  have : NeZero (Nat.card ↥tic.W2) := ⟨Nat.card_pos.ne'⟩
  let app : OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication tic :=
    ⟨tic.toDadeHypothesis.fullDadeIsometryData⟩
  let e : ↥tic.W ≃* ↥(h.W1 ⊔ h.W2) :=
    (Subgroup.subgroupOfEquivOfLe (typePData_W_le_self hyp.typeP)).symm.trans
      (MulEquiv.subgroupCongr (typePData_sup_subgroupOf_eq hyp.typeP).symm)
  have hvtic : v ∈ tic.V := hv
  have eaos : hyp.alignedOmegaSigmaGrid hG hodd i j v =
      (h.chiColumn χ₂ (finCongr hcardW1.symm i) :
        ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
        (e ⟨v, tic.V_subset_W hvtic⟩) := by
    unfold Hypothesis.alignedOmegaSigmaGrid
    rw [tic.sigmaIntegral_apply_of_mem_V rfl app _ hvtic,
      ClassFunction.compHom_apply]
    rfl
  have hsource : hyp.alignedOmegaSourceCharacter hG hodd i j =
      (h.sdiffTICyclicHypothesis.omegaProdChar
        (h.w1CharEquiv (finCongr hcardW1.symm i)) χ₂).comp e.toMonoidHom := by
    unfold Hypothesis.alignedOmegaSourceCharacter
    rfl
  rw [eaos, hsource]
  rfl

end OddOrder.Peterfalvi.S12
