-- Prove2me | solution 1 for ThreeSum.WeightedAddresses.digitCode_strict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:26:03.154163+00:00
-- url     : https://prove2.me/submissions/4dd5eb53-826b-43dd-9e9e-6314a32c7164

import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_Weighted_Enumeration
import Definitions.Def_Submission_Weighted_Addresses

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedAddresses
open ThreeSum.WeightedEnumeration
namespace ThreeSum.WeightedAddresses
theorem _root_.solution {d e : ℕ} (hd : d < 3) (he : e < 3) (hde : d < e) :
    digitCode d < digitCode e := by
  interval_cases d <;> interval_cases e <;> norm_num [digitCode] at *
end ThreeSum.WeightedAddresses
