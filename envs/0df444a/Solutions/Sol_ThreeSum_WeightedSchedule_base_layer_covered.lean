-- Prove2me | solution 1 for ThreeSum.WeightedSchedule.base_layer_covered
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:44:12.926577+00:00
-- url     : https://prove2.me/submissions/a74db418-f6cd-478e-b99e-7c2122c698de

import Definitions.Def_Submission_Weighted_BankEnumeration
import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Definitions.Def_Submission_Weighted_Schedule

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedSchedule
open TernaryJointType WeightedBankEnumeration
namespace ThreeSum.WeightedSchedule
theorem _root_.solution (m : ℕ) : 1025*sourceRank m≤2*bankCut m := by
  unfold sourceRank bankCut; omega
end ThreeSum.WeightedSchedule
