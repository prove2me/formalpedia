-- Prove2me | solution 1 for ThreeSum.WeightedGlobalFrontendResources.fixed_dimension_powerBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:42:55.653079+00:00
-- url     : https://prove2.me/submissions/69d98848-6a4b-4fb4-8c75-1ece3c2cf622

import Definitions.Def_Submission_Weighted_CountFrontend
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_Submission_Weighted_Global_TernaryRadixOverhead
import Definitions.Def_Submission_Weighted_Global_FrontendResources
import Theorems.Thm_ThreeSum_WeightedGlobalFrontendResources_radix_length_powerBound
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_const
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_mul


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
    PowerBound (fun n=>WeightedGlobalLocalParameters.fixedLength (radixLength m n*m)) 0 := by
  have hh:= (PowerBound.const (WeightedGlobalLocalParameters.fixedLength m)).mul (radix_length_powerBound hm)
  convert hh using 1
  · funext n; unfold WeightedGlobalLocalParameters.fixedLength; ring
  · norm_num
end ThreeSum.WeightedGlobalFrontendResources
