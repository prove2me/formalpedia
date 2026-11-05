-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalMomentReporterBudget.reporter_time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T13:38:53.311758+00:00
-- url     : https://prove2.me/submissions/d828f948-071a-4115-8396-a3c0ff6bcbfc

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryMomentReporter
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryMomentReporterBudget
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalMomentReporterBudget_driver_time_bound

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalMomentReporterBudget
open Light TernaryMomentSchedule TernaryWeightChannels
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalMomentReporterBudget
theorem _root_.solution {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N) (H : ℕ) :
    LightWeightedGlobalMomentReporter.time S H≤reporterConstant H*base S := by
  have hd := driver_time_bound S (2*H+1)
  have hB : 1≤base S := by unfold base; omega
  have hcount : S.front.count≤base S := by unfold base; omega
  have hrow := Nat.mul_le_mul_right (LightTernaryMomentRow.time H+200) hcount
  have hconst := Nat.mul_le_mul_left 500 hB
  unfold LightWeightedGlobalMomentReporter.time LightTernaryMomentBatch.time reporterConstant
  nlinarith only [hd,hrow,hconst]
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalMomentReporterBudget
