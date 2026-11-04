-- Prove2me | solution 1 for ThreeSum.WeightedGlobalFrontendResources.radix_length_powerBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:27:54.139463+00:00
-- url     : https://prove2.me/submissions/d47479a3-3e71-4d4f-a5cb-01426b9fb7b8

import Definitions.Def_Submission_Weighted_CountFrontend
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_Submission_Weighted_Global_TernaryRadixOverhead
import Definitions.Def_Submission_Weighted_Global_FrontendResources
import Theorems.Thm_ThreeSum_WeightedGlobalRadixOverhead_polynomial_radix_budget


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
    PowerBound (radixLength m) 0 := by
  intro δ hδ
  have hh:= WeightedGlobalRadixOverhead.polynomial_radix_budget hm 1 (by norm_num) 1 hδ
  filter_upwards [hh] with n hn
  norm_num at hn ⊢
  linarith
end ThreeSum.WeightedGlobalFrontendResources
