-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedFrontendResources.full_mask_powerBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T11:39:47.776746+00:00
-- url     : https://prove2.me/submissions/3dad790b-435c-46b3-9de0-a643e9064197

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_CountFrontend
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_Submission_ThreeSum_TernaryRadixOverhead
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_FrontendResources
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedFrontendResources_fixed_radix_powerBound
import Theorems.Thm_Light_MatAt_congr
import Theorems.Thm_Light_Seg_congr
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_congr


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedFrontendResources
open Light ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryEuler
open ThreeSum.LightWeightedNearPair ThreeSum.LightWeightedQueryPlan
open ThreeSum.WeightedBankStageModel ThreeSum.LightWeightedPreparedWanted
open Filter StageBounds ThreeSum.TernaryCodeSemantics
open scoped Topology
set_option maxHeartbeats 6000000
set_option maxRecDepth 18000
open ThreeSum.TernaryCoverScale ThreeSum.TernaryPrincipalDimensions
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedFrontendResources
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
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedFrontendResources
