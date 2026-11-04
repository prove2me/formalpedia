-- Prove2me | solution 1 for ThreeSum.MaskErase.eraseMask_ne_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:05:37.797463+00:00
-- url     : https://prove2.me/submissions/246d7fb1-f4d3-4b11-8aa0-0e3cc7a739c5

import Definitions.Def_Submission_ThreeSum_SubsetAddress
import Definitions.Def_Submission_ThreeSum_MaskErase
import Theorems.Thm_ThreeSum_MaskErase_eraseMask_subsetMask
import Theorems.Thm_ThreeSum_SubsetAddress_subsetMask_injective


set_option autoImplicit false
open ThreeSum ThreeSum.MaskErase
open Finset
open scoped BigOperators
open SubsetAddress
namespace ThreeSum.MaskErase
theorem _root_.solution {L : ℕ} (s : Finset (Fin L)) (a : Fin L) :
    eraseMask L a.val (subsetMask s) ≠ subsetMask s ↔ a ∈ s := by
  rw [eraseMask_subsetMask, (subsetMask_injective L).ne_iff, Finset.erase_ne_self]
end ThreeSum.MaskErase
