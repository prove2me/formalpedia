-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedSchedule.cacheCost_counts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:09:39.516127+00:00
-- url     : https://prove2.me/submissions/4f8c5c15-6456-4616-be47-41d46bd1feca

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
    cacheCost Q=1369*digitCount Q 1+2740*digitCount Q 2 := by
  unfold cacheCost WeightedCache.cost digitCount
  rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  generalize Q i=d
  fin_cases d <;> norm_num <;> decide
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedSchedule
