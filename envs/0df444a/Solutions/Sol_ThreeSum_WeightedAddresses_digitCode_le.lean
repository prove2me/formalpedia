-- Prove2me | solution 1 for ThreeSum.WeightedAddresses.digitCode_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:26:16.4634+00:00
-- url     : https://prove2.me/submissions/4dd3cba7-180f-4a40-a068-fad336296104

import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_Weighted_Enumeration
import Definitions.Def_Submission_Weighted_Addresses

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedAddresses
open ThreeSum.WeightedEnumeration
namespace ThreeSum.WeightedAddresses
theorem _root_.solution {d : ℕ} (hd : d < 3) : digitCode d ≤ 3 := by
  unfold digitCode
  split <;> omega
end ThreeSum.WeightedAddresses
