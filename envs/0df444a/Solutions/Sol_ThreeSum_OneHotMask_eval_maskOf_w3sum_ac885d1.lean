-- Prove2me | solution 1 for ThreeSum.OneHotMask.eval_maskOf_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:19:50.927671+00:00
-- url     : https://prove2.me/submissions/5f9b1fb2-cde3-41b9-a209-0d1d1d7b6eb8

import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Definitions.Def_Submission_ThreeSum_MaskErase
import Definitions.Def_Submission_ThreeSum_OneHotMask
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_maskOf_isMask
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero


namespace ThreeSum.OneHotMask
open Finset SubsetAddress LocalHashMoments
open scoped BigOperators
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
private theorem subset_range_pred {L : ℕ} {s : Finset ℕ}
    (hs : s ⊆ range (L+1)) (hL : L ∉ s) : s ⊆ range L := by
  intro i hi
  have h := mem_range.mp (hs hi)
  have hn : i ≠ L := by rintro rfl; exact hL hi
  exact mem_range.mpr (by omega)
end ThreeSum.OneHotMask
set_option autoImplicit false
open ThreeSum ThreeSum.OneHotMask
open Finset SubsetAddress LocalHashMoments
open scoped BigOperators
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
namespace ThreeSum.OneHotMask
theorem _root_.solution {L : ℕ} (s : Finset ℕ) (hs : s ⊆ range L)
    (w0 w1 : ℕ → ℕ) :
    eval w0 w1 L (maskOf s) = ∑ i ∈ range L, if i ∈ s then w1 i else w0 i := by
  induction L generalizing s with
  | zero => simp [eval]
  | succ L ih =>
    by_cases hL : L ∈ s
    · have ht : s.erase L ⊆ range L :=
        subset_range_pred ((erase_subset L s).trans hs) (notMem_erase _ _)
      have he : 2^L + maskOf (s.erase L) = maskOf s :=
        add_sum_erase s (fun i => 2^i) hL
      have hlo : ¬maskOf s < 2^L := by omega
      have hsub : maskOf s-2^L = maskOf (s.erase L) := by omega
      rw [eval, if_neg hlo, hsub, ih (s.erase L) ht, sum_range_succ, if_pos hL]
      congr 1
      apply sum_congr rfl
      intro i hi
      have hiL : i ≠ L := by have := mem_range.mp hi; omega
      by_cases hiS : i ∈ s <;> simp [hiS, hiL]
    · have ht := subset_range_pred hs hL
      have hlo := (maskOf_isMask ht).1
      rw [eval, if_pos hlo, ih s ht, sum_range_succ, if_neg hL]
end ThreeSum.OneHotMask
