-- Prove2me | solution 1 for ThreeSum.WeightedSchedule.rank_counts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:12:54.153552+00:00
-- url     : https://prove2.me/submissions/d3dc56f8-a735-454d-8c68-ca4ce18a1732

import Definitions.Def_Submission_Weighted_BankEnumeration
import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Definitions.Def_Submission_Weighted_Schedule

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedSchedule
open TernaryJointType WeightedBankEnumeration
namespace ThreeSum.WeightedSchedule
theorem _root_.solution {N : ℕ} (Q : TritWord N) :
    TernaryBank.rank Q=digitCount Q 1+2*digitCount Q 2 := by
  unfold TernaryBank.rank digitCount
  rw [Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  generalize Q i=d
  fin_cases d <;> norm_num <;> decide
end ThreeSum.WeightedSchedule
