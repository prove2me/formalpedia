-- Prove2me | solution 1 for ThreeSum.WeightedFrontendResources.fixed_dimension_powerBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:54:04.192385+00:00
-- url     : https://prove2.me/submissions/4f5e4d49-3a2a-4bc1-9e23-aedcc94baa58

import Definitions.Def_Submission_Weighted_CountFrontend
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_Submission_ThreeSum_TernaryRadixOverhead
import Definitions.Def_Submission_Weighted_FrontendResources
import Theorems.Thm_ThreeSum_WeightedFrontendResources_radix_length_powerBound
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_const
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_mul


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
    PowerBound (fun n=>TernaryLocalParameters.fixedLength (radixLength m n*m)) 0 := by
  have hh:= (PowerBound.const (TernaryLocalParameters.fixedLength m)).mul (radix_length_powerBound hm)
  convert hh using 1
  · funext n; unfold TernaryLocalParameters.fixedLength; ring
  · norm_num
end ThreeSum.WeightedFrontendResources
