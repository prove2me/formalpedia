-- Prove2me | solution 1 for ThreeSum.WeightedSchedule.same_type_cost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:44:10.563114+00:00
-- url     : https://prove2.me/submissions/e9b99db4-12db-463b-9f4b-f52809a3f42a

import Definitions.Def_Submission_Weighted_BankEnumeration
import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Definitions.Def_Submission_Weighted_Schedule
import Theorems.Thm_ThreeSum_WeightedSchedule_cacheCost_counts

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedSchedule
open TernaryJointType WeightedBankEnumeration
namespace ThreeSum.WeightedSchedule
theorem _root_.solution {N : ℕ} {Q R : TritWord N} {π : DigitType}
    (hQ : HasType Q π) (hR : HasType R π) : cacheCost Q=cacheCost R := by
  rw [cacheCost_counts,cacheCost_counts,hQ 1,hQ 2,hR 1,hR 2]
end ThreeSum.WeightedSchedule
