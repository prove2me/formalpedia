-- Prove2me | solution 1 for ThreeSum.BoxStages.partialZeta_eq_boxSum_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:36:07.288222+00:00
-- url     : https://prove2.me/submissions/4ab2dc64-17f3-4fb0-8363-a0f9996d318b

import Definitions.Def_Submission_ThreeSum_SubsetStages
import Definitions.Def_Submission_ThreeSum_SparseBoxes
import Definitions.Def_Submission_ThreeSum_BoxStages
import Theorems.Thm_ThreeSum_BoxStages_mem_prefix
import Theorems.Thm_ThreeSum_BoxStages_prefix_zero
import Theorems.Thm_ThreeSum_BoxStages_prefix_all
import Theorems.Thm_ThreeSum_BoxStages_stageValue_zero
import Theorems.Thm_ThreeSum_BoxStages_stageValue_all
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_SubsetStages_mem_suffix
import Theorems.Thm_ThreeSum_SubsetStages_stageValue_all
import Theorems.Thm_ThreeSum_SubsetStages_stageValue_zero
import Theorems.Thm_ThreeSum_SubsetStages_suffix_all
import Theorems.Thm_ThreeSum_SubsetStages_suffix_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.SubsetStages.mem_suffix
attribute [local simp] ThreeSum.SubsetStages.stageValue_all
attribute [local simp] ThreeSum.SubsetStages.stageValue_zero
attribute [local simp] ThreeSum.SubsetStages.suffix_all
attribute [local simp] ThreeSum.SubsetStages.suffix_zero


attribute [local simp] ThreeSum.BoxStages.mem_prefix
attribute [local simp] ThreeSum.BoxStages.prefix_zero
attribute [local simp] ThreeSum.BoxStages.prefix_all
attribute [local simp] ThreeSum.BoxStages.stageValue_zero
attribute [local simp] ThreeSum.BoxStages.stageValue_all

set_option autoImplicit false
open ThreeSum ThreeSum.BoxStages
open Finset
namespace ThreeSum.BoxStages
theorem _root_.solution {L : ℕ} (weight : Finset (Fin L) → ℤ)
    (flags processed : Finset (Fin L)) :
    Subset.partialZeta processed weight flags =
      SparseBoxes.boxSum flags (flags ∩ processed) weight := by
  have hrequired : flags \ (flags ∩ processed) = flags \ processed := by
    ext a
    simp only [mem_sdiff,mem_inter]
    tauto
  unfold Subset.partialZeta SparseBoxes.boxSum
  rw [hrequired,← Finset.sum_filter]
  apply Finset.sum_bij (fun x _ => (flags \ processed) ∪ x)
  · intro x hx
    have hsub := Finset.mem_powerset.mp hx
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr ?_,Finset.subset_union_left⟩
    exact Finset.union_subset Finset.sdiff_subset (hsub.trans Finset.inter_subset_left)
  · intro x hx y hy he
    have hxp := (Finset.mem_powerset.mp hx).trans Finset.inter_subset_right
    have hyp := (Finset.mem_powerset.mp hy).trans Finset.inter_subset_right
    ext a
    constructor
    · intro ha
      have he' : a ∈ (flags \ processed) ∪ y := he ▸ Finset.mem_union_right _ ha
      rcases Finset.mem_union.mp he' with hh | hh
      · exact False.elim ((Finset.mem_sdiff.mp hh).2 (hxp ha))
      · exact hh
    · intro ha
      have he' : a ∈ (flags \ processed) ∪ x := he.symm ▸ Finset.mem_union_right _ ha
      rcases Finset.mem_union.mp he' with hh | hh
      · exact False.elim ((Finset.mem_sdiff.mp hh).2 (hyp ha))
      · exact hh
  · intro leaf hl
    obtain ⟨hleaf,hrequired⟩ := Finset.mem_filter.mp hl
    have hlf := Finset.mem_powerset.mp hleaf
    refine ⟨leaf ∩ processed,Finset.mem_powerset.mpr ?_,?_⟩
    · intro a ha
      exact Finset.mem_inter.mpr ⟨hlf (Finset.mem_inter.mp ha).1,(Finset.mem_inter.mp ha).2⟩
    · ext a
      simp only [mem_union,mem_sdiff,mem_inter]
      constructor
      · rintro (⟨haf,hap⟩ | ⟨hal,hap⟩)
        · exact hrequired (Finset.mem_sdiff.mpr ⟨haf,hap⟩)
        · exact hal
      · intro hal
        by_cases hap : a ∈ processed
        · exact Or.inr ⟨hal,hap⟩
        · exact Or.inl ⟨hlf hal,hap⟩
  · intro x hx
    rfl
end ThreeSum.BoxStages
