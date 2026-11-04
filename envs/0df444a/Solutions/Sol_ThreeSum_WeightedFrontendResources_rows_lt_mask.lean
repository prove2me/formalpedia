-- Prove2me | solution 1 for ThreeSum.WeightedFrontendResources.rows_lt_mask
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:53:42.653663+00:00
-- url     : https://prove2.me/submissions/2a29b6b7-9d7b-4e8a-b9e1-8b4d07a0e6bb

import Definitions.Def_Submission_Weighted_CountFrontend
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_Submission_ThreeSum_TernaryRadixOverhead
import Definitions.Def_Submission_Weighted_FrontendResources
import Theorems.Thm_ThreeSum_WeightedFrontendResources_rows_le_full
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_rows
attribute [local simp] ThreeSum.LightWeightedCountFrontend.rows



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
namespace ThreeSum.WeightedFrontendResources
theorem _root_.solution {N : ℕ} (hN : 0<N) (Q : TritWord N) (T : ℕ) :
    rows Q T<2^(2*N) := by
  have hpow : (3:ℕ)^N<4^N := Nat.pow_lt_pow_left (by decide) (by omega)
  have he : 2^(2*N)=4^N := by rw [pow_mul]; norm_num
  rw [he]
  exact (rows_le_full Q T).trans_lt hpow
end ThreeSum.WeightedFrontendResources
