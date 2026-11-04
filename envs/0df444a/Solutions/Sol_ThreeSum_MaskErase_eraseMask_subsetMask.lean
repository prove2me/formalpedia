-- Prove2me | solution 1 for ThreeSum.MaskErase.eraseMask_subsetMask
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:59:37.097007+00:00
-- url     : https://prove2.me/submissions/6ba0bf99-853e-46a3-b40f-64bf0f385464

import Definitions.Def_Submission_ThreeSum_SubsetAddress
import Definitions.Def_Submission_ThreeSum_MaskErase
import Definitions.Def_WeightedCache3SUM_Alias_c15dd3b5e05b2f5c
import Theorems.Thm_ThreeSum_MaskErase_natPositions_erase
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_subset


set_option autoImplicit false
open ThreeSum ThreeSum.MaskErase
open Finset
open scoped BigOperators
open SubsetAddress
namespace ThreeSum.MaskErase
theorem _root_.solution {L : ℕ} (s : Finset (Fin L)) (a : Fin L) :
    eraseMask L a.val (subsetMask s) = subsetMask (s.erase a) := by
  rw [subsetMask, eraseMask_maskOf _ (natPositions_subset s),
    ← natPositions_erase, ← subsetMask]
end ThreeSum.MaskErase
