-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedFrontendResources.fixed_dimension_powerBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T11:29:46.242409+00:00
-- url     : https://prove2.me/submissions/0ad5a012-3c9c-4897-ab03-f9269ddffefc

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_CountFrontend
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_Submission_ThreeSum_TernaryRadixOverhead
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_FrontendResources
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedFrontendResources_radix_length_powerBound
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_const
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_mul


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
    PowerBound (fun n=>TernaryLocalParameters.fixedLength (radixLength m n*m)) 0 := by
  have hh:= (PowerBound.const (TernaryLocalParameters.fixedLength m)).mul (radix_length_powerBound hm)
  convert hh using 1
  · funext n; unfold TernaryLocalParameters.fixedLength; ring
  · norm_num
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedFrontendResources
