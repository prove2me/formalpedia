-- Prove2me | solution 1 for ThreeSum.WeightedGlobalMomentReporterBudget.reporter_time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T16:22:10.711851+00:00
-- url     : https://prove2.me/submissions/66be441c-190c-4590-8599-f4ca0cc88b39

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryMomentReporter
import Definitions.Def_Submission_Weighted_Global_TernaryMomentReporterBudget
import Theorems.Thm_ThreeSum_WeightedGlobalMomentReporterBudget_driver_time_bound

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalMomentReporterBudget
open Light TernaryMomentSchedule TernaryWeightChannels
namespace ThreeSum.WeightedGlobalMomentReporterBudget
theorem _root_.solution {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N) (H : ℕ) :
    LightWeightedGlobalMomentReporter.time S H≤reporterConstant H*base S := by
  have hd := driver_time_bound S (2*H+1)
  have hB : 1≤base S := by unfold base; omega
  have hcount : S.front.count≤base S := by unfold base; omega
  have hrow := Nat.mul_le_mul_right (LightTernaryMomentRow.time H+200) hcount
  have hconst := Nat.mul_le_mul_left 500 hB
  unfold LightWeightedGlobalMomentReporter.time LightTernaryMomentBatch.time reporterConstant
  nlinarith only [hd,hrow,hconst]
end ThreeSum.WeightedGlobalMomentReporterBudget
