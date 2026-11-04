-- Prove2me | solution 1 for ThreeSum.WeightedFrontendResources.full_mask_powerBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:16:34.723764+00:00
-- url     : https://prove2.me/submissions/a0272042-248c-40c2-8c17-661df9f02764

import Definitions.Def_Submission_Weighted_CountFrontend
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_Submission_ThreeSum_TernaryRadixOverhead
import Definitions.Def_Submission_Weighted_FrontendResources
import Theorems.Thm_ThreeSum_WeightedFrontendResources_fixed_radix_powerBound
import Theorems.Thm_Light_MatAt_congr
import Theorems.Thm_Light_Seg_congr
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_congr


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedFrontendResources
open Light ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryEuler
open ThreeSum.LightWeightedNearPair ThreeSum.LightWeightedQueryPlan
open ThreeSum.WeightedBankStageModel ThreeSum.LightWeightedPreparedWanted
open Filter StageBounds ThreeSum.TernaryCodeSemantics
open scoped Topology
set_option maxHeartbeats 6000000
set_option maxRecDepth 18000
open ThreeSum.TernaryCoverScale ThreeSum.TernaryPrincipalDimensions
namespace ThreeSum.WeightedFrontendResources
theorem _root_.solution {m : ℕ} (hm : 0< m) :
    PowerBound (fun n=>4^TernaryLocalParameters.fixedLength (radixLength m n*m))
      (2*Real.log (4^TernaryLocalParameters.fixedLength m:ℕ)/Real.log (outputSize m:ℝ)) := by
  have hpos : 0< 4^TernaryLocalParameters.fixedLength m := by positivity
  have hh:= fixed_radix_powerBound hm (4^TernaryLocalParameters.fixedLength m-1)
  have hbase : 4^TernaryLocalParameters.fixedLength m-1+1=4^TernaryLocalParameters.fixedLength m := by omega
  rw [hbase] at hh
  convert hh using 1
  funext n
  rw [←pow_mul]
  congr 1
  unfold TernaryLocalParameters.fixedLength
  ring
end ThreeSum.WeightedFrontendResources
