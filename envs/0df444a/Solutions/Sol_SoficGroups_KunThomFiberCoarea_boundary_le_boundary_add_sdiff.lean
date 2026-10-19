-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.boundary_le_boundary_add_sdiff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.923416+00:00
-- url     : https://prove2.me/submissions/c3f016d4-8080-4b64-b773-8801c589786f

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea
namespace SoficGroups.KunThomFiberCoarea
theorem _root_.solution
    {V ι : Type*} [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (U W : Finset V) :
    SoficGroups.boundary σ U ≤ SoficGroups.boundary σ W +
      Fintype.card ι * ((U \ W).card + (W \ U).card) := by
  classical
  have hpoint (i : ι) :
      (U.filter fun x => σ i x ∉ U).card ≤
        (W.filter fun x => σ i x ∉ W).card +
          (U \ W).card + (W \ U).card := by
    let BU := U.filter fun x => σ i x ∉ U
    let BW := W.filter fun x => σ i x ∉ W
    let E := U \ W
    let C := (W \ U).image (σ i).symm
    have hC : C.card = (W \ U).card := by
      dsimp [C]
      exact Finset.card_image_of_injective _ (σ i).symm.injective
    have hsub : BU ⊆ (BW ∪ E) ∪ C := by
      intro x hx
      obtain ⟨hxU, hxout⟩ := Finset.mem_filter.mp hx
      by_cases hxW : x ∈ W
      · by_cases himage : σ i x ∈ W
        · apply Finset.mem_union_right
          apply Finset.mem_image.mpr
          refine ⟨σ i x, Finset.mem_sdiff.mpr ⟨himage, hxout⟩, ?_⟩
          simp
        · apply Finset.mem_union_left
          apply Finset.mem_union_left
          exact Finset.mem_filter.mpr ⟨hxW, himage⟩
      · apply Finset.mem_union_left
        apply Finset.mem_union_right
        exact Finset.mem_sdiff.mpr ⟨hxU, hxW⟩
    change BU.card ≤ BW.card + (U \ W).card + (W \ U).card
    calc
      BU.card ≤ ((BW ∪ E) ∪ C).card := Finset.card_le_card hsub
      _ ≤ (BW ∪ E).card + C.card := Finset.card_union_le _ _
      _ ≤ (BW.card + E.card) + C.card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ = BW.card + (U \ W).card + (W \ U).card := by
        rw [hC]
  unfold SoficGroups.boundary
  calc
    (∑ i : ι, (U.filter fun x => σ i x ∉ U).card) ≤
        ∑ i : ι,
          ((W.filter fun x => σ i x ∉ W).card +
            (U \ W).card + (W \ U).card) := by
          apply Finset.sum_le_sum
          intro i _
          exact hpoint i
    _ = (∑ i : ι, (W.filter fun x => σ i x ∉ W).card) +
          Fintype.card ι * ((U \ W).card + (W \ U).card) := by
          simp [Finset.sum_add_distrib, mul_add, add_assoc]
end SoficGroups.KunThomFiberCoarea
