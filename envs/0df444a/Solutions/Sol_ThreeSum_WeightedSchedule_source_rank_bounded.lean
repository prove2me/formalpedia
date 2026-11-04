-- Prove2me | solution 1 for ThreeSum.WeightedSchedule.source_rank_bounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:44:14.224408+00:00
-- url     : https://prove2.me/submissions/48b232fa-7577-4b66-b5fa-9f6b26be48f0

import Definitions.Def_Submission_Weighted_BankEnumeration
import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Definitions.Def_Submission_Weighted_Schedule

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedSchedule
open TernaryJointType WeightedBankEnumeration
namespace ThreeSum.WeightedSchedule
theorem _root_.solution (m : ℕ) : sourceRank m≤2*fixedLength m := by
  unfold sourceRank fixedLength; omega
end ThreeSum.WeightedSchedule
