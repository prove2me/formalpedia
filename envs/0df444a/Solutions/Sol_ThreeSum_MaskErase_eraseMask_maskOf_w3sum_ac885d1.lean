-- Prove2me | solution 1 for ThreeSum.MaskErase.eraseMask_maskOf_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:09:19.507211+00:00
-- url     : https://prove2.me/submissions/b943c2e6-eb41-438f-9147-71974c7450cb

import Definitions.Def_Submission_ThreeSum_SubsetAddress
import Definitions.Def_Submission_ThreeSum_MaskErase
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_maskOf_isMask
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero


namespace ThreeSum.MaskErase
open Finset
open scoped BigOperators
open SubsetAddress
private theorem subset_range_pred {L : ℕ} {s : Finset ℕ}
    (hs : s ⊆ Finset.range (L+1)) (hL : L ∉ s) : s ⊆ Finset.range L := by
  intro i hi
  have h := Finset.mem_range.mp (hs hi)
  have hn : i ≠ L := by rintro rfl; exact hL hi
  exact Finset.mem_range.mpr (by omega)
end ThreeSum.MaskErase
set_option autoImplicit false
open ThreeSum ThreeSum.MaskErase
open Finset
open scoped BigOperators
open SubsetAddress
namespace ThreeSum.MaskErase
theorem _root_.solution {L : ℕ} (s : Finset ℕ) (hs : s ⊆ Finset.range L) (a : ℕ) :
    eraseMask L a (maskOf s) = maskOf (s.erase a) := by
  induction L generalizing s with
  | zero =>
    have he : s = ∅ := by simpa using hs
    subst s
    simp [eraseMask, maskOf]
  | succ L ih =>
    by_cases hL : L ∈ s
    · have ht : s.erase L ⊆ Finset.range L :=
        subset_range_pred ((Finset.erase_subset L s).trans hs) (Finset.notMem_erase _ _)
      have he : 2^L + maskOf (s.erase L) = maskOf s :=
        Finset.add_sum_erase s (fun i => 2^i) hL
      have hb := (maskOf_isMask ht).1
      have hlo : ¬maskOf s < 2^L := by omega
      rw [eraseMask, if_neg hlo]
      have hsub : maskOf s - 2^L = maskOf (s.erase L) := by omega
      rw [hsub]
      by_cases ha : a = L
      · simp only [ha, ite_true]
      · rw [if_neg ha, ih (s.erase L) ht]
        have hL' : L ∈ s.erase a := Finset.mem_erase.mpr ⟨Ne.symm ha, hL⟩
        have heer : (s.erase L).erase a = (s.erase a).erase L := by
          ext i
          simp only [Finset.mem_erase]
          tauto
        rw [heer]
        exact Finset.add_sum_erase (s.erase a) (fun i => 2^i) hL'
    · have hs' := subset_range_pred hs hL
      have hlo := (maskOf_isMask hs').1
      rw [eraseMask, if_pos hlo]
      exact ih s hs'
end ThreeSum.MaskErase
