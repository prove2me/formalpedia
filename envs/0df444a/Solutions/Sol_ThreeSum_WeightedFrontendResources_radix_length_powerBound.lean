-- Prove2me | solution 1 for ThreeSum.WeightedFrontendResources.radix_length_powerBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:31:01.766436+00:00
-- url     : https://prove2.me/submissions/c55e6538-a530-4b66-9d41-36831498cb81

import Definitions.Def_Submission_Weighted_CountFrontend
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_Submission_ThreeSum_TernaryRadixOverhead
import Definitions.Def_Submission_Weighted_FrontendResources
import Theorems.Thm_ThreeSum_TernaryRadixOverhead_polynomial_radix_budget


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
    PowerBound (radixLength m) 0 := by
  intro δ hδ
  have hh:= TernaryRadixOverhead.polynomial_radix_budget hm 1 (by norm_num) 1 hδ
  filter_upwards [hh] with n hn
  norm_num at hn ⊢
  linarith
end ThreeSum.WeightedFrontendResources
