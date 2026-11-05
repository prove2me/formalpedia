-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedSchedule.rank_counts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:09:40.097872+00:00
-- url     : https://prove2.me/submissions/b6b2ba12-b5ef-451b-8e59-e5ec9e3f8fb3

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Schedule

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedSchedule
open TernaryJointType WeightedBankEnumeration
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedSchedule
theorem _root_.solution {N : ℕ} (Q : TritWord N) :
    TernaryBank.rank Q=digitCount Q 1+2*digitCount Q 2 := by
  unfold TernaryBank.rank digitCount
  rw [Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  generalize Q i=d
  fin_cases d <;> norm_num <;> decide
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedSchedule
