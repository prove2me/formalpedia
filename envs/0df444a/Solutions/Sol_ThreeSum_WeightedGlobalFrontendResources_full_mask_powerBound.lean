-- Prove2me | solution 1 for ThreeSum.WeightedGlobalFrontendResources.full_mask_powerBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:45:19.346352+00:00
-- url     : https://prove2.me/submissions/b4cc71cf-d8d9-4232-b009-c50dc5b330dd

import Definitions.Def_Submission_Weighted_CountFrontend
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_Submission_Weighted_Global_TernaryRadixOverhead
import Definitions.Def_Submission_Weighted_Global_FrontendResources
import Theorems.Thm_ThreeSum_WeightedGlobalFrontendResources_fixed_radix_powerBound
import Theorems.Thm_Light_MatAt_congr
import Theorems.Thm_Light_Seg_congr
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_congr


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalFrontendResources
open Light ThreeSum.TernaryJointType ThreeSum.WeightedGlobalBank ThreeSum.TernaryEuler
open ThreeSum.LightWeightedNearPair ThreeSum.LightWeightedQueryPlan
open ThreeSum.WeightedBankStageModel ThreeSum.LightWeightedPreparedWanted
open Filter StageBounds ThreeSum.TernaryCodeSemantics
open scoped Topology
set_option maxHeartbeats 6000000
set_option maxRecDepth 18000
open ThreeSum.WeightedGlobalCoverScale ThreeSum.WeightedGlobalPrincipalDimensions
namespace ThreeSum.WeightedGlobalFrontendResources
theorem _root_.solution {m : ℕ} (hm : 0< m) :
    PowerBound (fun n=>4^WeightedGlobalLocalParameters.fixedLength (radixLength m n*m))
      (2*Real.log (4^WeightedGlobalLocalParameters.fixedLength m:ℕ)/Real.log (outputSize m:ℝ)) := by
  have hpos : 0< 4^WeightedGlobalLocalParameters.fixedLength m := by positivity
  have hh:= fixed_radix_powerBound hm (4^WeightedGlobalLocalParameters.fixedLength m-1)
  have hbase : 4^WeightedGlobalLocalParameters.fixedLength m-1+1=4^WeightedGlobalLocalParameters.fixedLength m := by omega
  rw [hbase] at hh
  convert hh using 1
  funext n
  rw [←pow_mul]
  congr 1
  unfold WeightedGlobalLocalParameters.fixedLength
  ring
end ThreeSum.WeightedGlobalFrontendResources
