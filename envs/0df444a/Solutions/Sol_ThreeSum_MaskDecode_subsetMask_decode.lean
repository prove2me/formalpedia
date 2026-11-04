-- Prove2me | solution 1 for ThreeSum.MaskDecode.subsetMask_decode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:09:20.601681+00:00
-- url     : https://prove2.me/submissions/ea1fe937-84c8-4802-aa8c-b159eae10493

import Definitions.Def_Submission_ThreeSum_SubsetAddress
import Definitions.Def_Submission_ThreeSum_MaskDecode
import Theorems.Thm_ThreeSum_MaskDecode_natPositions_decode

set_option autoImplicit false
open ThreeSum ThreeSum.MaskDecode
open Finset
open scoped BigOperators
open SubsetAddress
namespace ThreeSum.MaskDecode
theorem _root_.solution {L m : ℕ} (hm : m < 2^L) : subsetMask (decode L m) = m := by
  rw [subsetMask, natPositions_decode hm, maskOf]
  exact Finset.sum_toFinset_bitIndices_two_pow m
end ThreeSum.MaskDecode
