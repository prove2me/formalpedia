-- Prove2me | solution 1 for ThreeSum.LightTernaryCodes.digit_le_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:53:23.17354+00:00
-- url     : https://prove2.me/submissions/ef5ddb07-8e0c-46b9-9ab7-783acf4fe709

import Definitions.Def_Submission_ThreeSum_LightMaskErase
import Definitions.Def_Submission_ThreeSum_LightMaskBits
import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Theorems.Thm_ThreeSum_LightMaskBits_bit_le
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_high
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low


set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryCodes
open Light ThreeSum.LightSubsetAddress ThreeSum.MaskErase
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightTernaryCodes
theorem _root_.solution (W low high m : ℕ) : digit W low high m ≤ 2 := by
  have h0 := LightMaskBits.bit_le W m low
  have h1 := LightMaskBits.bit_le W m high
  unfold digit
  omega
end ThreeSum.LightTernaryCodes
