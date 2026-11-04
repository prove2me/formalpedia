-- Prove2me | solution 1 for ThreeSum.MaskDecode.decode_subsetMask
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:13:31.338885+00:00
-- url     : https://prove2.me/submissions/f54c1d6f-0a11-4511-92a4-105b405b8878

import Definitions.Def_Submission_ThreeSum_SubsetAddress
import Definitions.Def_Submission_ThreeSum_MaskDecode
import Theorems.Thm_ThreeSum_MaskDecode_subsetMask_decode
import Theorems.Thm_ThreeSum_SubsetAddress_subsetMask_injective
import Theorems.Thm_ThreeSum_SubsetAddress_subsetMask_isMask


set_option autoImplicit false
open ThreeSum ThreeSum.MaskDecode
open Finset
open scoped BigOperators
open SubsetAddress
namespace ThreeSum.MaskDecode
theorem _root_.solution {L : ℕ} (s : Finset (Fin L)) : decode L (subsetMask s) = s := by
  apply subsetMask_injective L
  exact subsetMask_decode (subsetMask_isMask s).1
end ThreeSum.MaskDecode
