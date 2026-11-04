-- Prove2me | solution 1 for ThreeSum.MaskErase.eraseMask_le_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:07:27.886203+00:00
-- url     : https://prove2.me/submissions/27b120ea-c10a-4a56-a722-add395594eb6

import Definitions.Def_Submission_ThreeSum_SubsetAddress
import Definitions.Def_Submission_ThreeSum_MaskErase
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero



set_option autoImplicit false
open ThreeSum ThreeSum.MaskErase
open Finset
open scoped BigOperators
open SubsetAddress
namespace ThreeSum.MaskErase
theorem _root_.solution {L a m : ℕ} (hm : m < 2^L) : eraseMask L a m ≤ m := by
  induction L generalizing m with
  | zero => simp [eraseMask]
  | succ L ih =>
    by_cases hlo : m < 2^L
    · simpa only [eraseMask, hlo, ite_true] using ih hlo
    · have hm' : m-2^L < 2^L := by rw [pow_succ] at hm; omega
      rw [eraseMask, if_neg hlo]
      split
      · exact Nat.sub_le _ _
      · have hh := ih hm'
        omega
end ThreeSum.MaskErase
