-- Prove2me | solution 1 for ThreeSum.WeightedSchedule.cacheCost_counts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:12:53.107459+00:00
-- url     : https://prove2.me/submissions/424391dc-0104-4c4d-baac-75852061fb63

import Definitions.Def_Submission_Weighted_BankEnumeration
import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Definitions.Def_Submission_Weighted_Schedule

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedSchedule
open TernaryJointType WeightedBankEnumeration
namespace ThreeSum.WeightedSchedule
theorem _root_.solution {N : ℕ} (Q : TritWord N) :
    cacheCost Q=512*digitCount Q 1+1025*digitCount Q 2 := by
  unfold cacheCost WeightedCache.cost digitCount
  rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  generalize Q i=d
  fin_cases d <;> norm_num <;> decide
end ThreeSum.WeightedSchedule
