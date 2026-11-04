-- Prove2me | solution 1 for ThreeSum.WeightedQueryBudget.actual_query_time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:58:53.267208+00:00
-- url     : https://prove2.me/submissions/bb91342c-278a-49dd-9a1b-16fdb0ded0f3

import Definitions.Def_Submission_Weighted_PreparedWanted
import Definitions.Def_Submission_Weighted_Schedule
import Definitions.Def_Submission_Weighted_Parameters
import Definitions.Def_Submission_Weighted_QueryBudget
import Theorems.Thm_ThreeSum_WeightedQueryBudget_z_pos
import Theorems.Thm_ThreeSum_WeightedQueryBudget_z_lt_one
import Theorems.Thm_ThreeSum_WeightedQueryBudget_gibbs_expression
import Theorems.Thm_ThreeSum_LightWeightedFrozenQuery_queryTime_gibbs
import Theorems.Thm_ThreeSum_WeightedSchedule_query_boundary


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedQueryBudget
open Real TernaryJointType WeightedSchedule WeightedCacheParameters
open WeightedBankEnumeration (cacheCost)
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000
namespace ThreeSum.WeightedQueryBudget
theorem _root_.solution {m L : ℕ} (Q : TritWord (fixedLength m))
    (hQ : HasType Q (fixedPi m)) :
    (LightWeightedFrozenQuery.queryTime L (bankCut m) (fixedLength m) Q : ℝ)≤
      10000*((fixedLength m : ℝ)+L+1)*((fixedLength m : ℝ)+1)*envelope m := by
  have hg := LightWeightedFrozenQuery.queryTime_gibbs L (bankCut m) Q zRoot z_pos.le z_lt_one.le
  change _*zRoot^(cacheCost Q+1024-bankCut m)≤_ at hg
  rw [query_boundary hQ] at hg
  have hh := (le_div_iff₀ (pow_pos z_pos (treeBudget m))).mpr hg
  calc
    _≤_ := hh
    _=10000*((fixedLength m : ℝ)+L+1)*((fixedLength m : ℝ)+1)*envelope m := by
      rw [←gibbs_expression Q hQ]
      unfold queryArg1 queryArg2
      ring
end ThreeSum.WeightedQueryBudget
