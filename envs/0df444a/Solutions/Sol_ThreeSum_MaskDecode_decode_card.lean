-- Prove2me | solution 1 for ThreeSum.MaskDecode.decode_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:13:32.355656+00:00
-- url     : https://prove2.me/submissions/3a083a46-96e9-4ded-94dc-e732c3f410da

import Definitions.Def_Submission_ThreeSum_SubsetAddress
import Definitions.Def_Submission_ThreeSum_MaskDecode
import Theorems.Thm_ThreeSum_MaskDecode_subsetMask_decode
import Theorems.Thm_ThreeSum_SubsetAddress_subsetMask_isMask


set_option autoImplicit false
open ThreeSum ThreeSum.MaskDecode
open Finset
open scoped BigOperators
open SubsetAddress
namespace ThreeSum.MaskDecode
theorem _root_.solution {L m : ℕ} (hm : m < 2^L) : (decode L m).card = weight L m := by
  have h := (subsetMask_isMask (decode L m)).2
  rw [subsetMask_decode hm] at h
  exact h.symm
end ThreeSum.MaskDecode
