-- Prove2me | solution 1 for ThreeSum.LightMaskBits.bit_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:51:14.05903+00:00
-- url     : https://prove2.me/submissions/b9f06a4c-7ac4-4654-aa81-2fc7f73d0ad7

import Definitions.Def_Submission_ThreeSum_LightMaskErase
import Definitions.Def_Submission_ThreeSum_MaskDecode
import Definitions.Def_Submission_ThreeSum_LightMaskBits

set_option autoImplicit false
open ThreeSum ThreeSum.LightMaskBits
open Light LightSubsetAddress MaskErase
namespace ThreeSum.LightMaskBits
theorem _root_.solution (L m j : ℕ) : bit L m j ≤ 1 := by unfold bit; split <;> omega
end ThreeSum.LightMaskBits
