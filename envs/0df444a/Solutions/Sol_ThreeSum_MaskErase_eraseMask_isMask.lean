-- Prove2me | solution 1 for ThreeSum.MaskErase.eraseMask_isMask
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:07:06.367555+00:00
-- url     : https://prove2.me/submissions/9ad762a5-3ef9-40c9-b578-10e53c71341f

import Definitions.Def_Submission_ThreeSum_SubsetAddress
import Definitions.Def_Submission_ThreeSum_MaskErase
import Theorems.Thm_ThreeSum_MaskErase_eraseMask_subsetMask
import Theorems.Thm_ThreeSum_SubsetAddress_subsetMask_isMask


set_option autoImplicit false
open ThreeSum ThreeSum.MaskErase
open Finset
open scoped BigOperators
open SubsetAddress
namespace ThreeSum.MaskErase
theorem _root_.solution {L : ℕ} (s : Finset (Fin L)) (a : Fin L) (ha : a ∈ s) :
    IsMask L (s.card-1) (eraseMask L a.val (subsetMask s)) := by
  rw [eraseMask_subsetMask, ← Finset.card_erase_of_mem ha]
  exact subsetMask_isMask (s.erase a)
end ThreeSum.MaskErase
