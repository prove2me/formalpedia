-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaFrontendResources.word_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:45:45.396772+00:00
-- url     : https://prove2.me/submissions/f92298fc-7647-4e3e-b010-0f6e51b52110

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLayout
import Definitions.Def_Submission_Weighted_Global_FrontendResources
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFrontendResources

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaFrontendResources
open Light WeightedGlobalArenaLayout TernaryJointType WeightedGlobalBank TernaryEuler
open WeightedGlobalFrontendResources LightWeightedNearPair LightWeightedQueryPlan
open LightWeightedPreparedWanted WeightedBankStageModel TernaryCodeSemantics
set_option maxHeartbeats 6000000
namespace ThreeSum.WeightedGlobalArenaFrontendResources
theorem _root_.solution (N nb groups count R A : ℕ) :
    10000*(N+R+100)≤word N nb groups count R A := by
  unfold word
  generalize (N+1)*nb=s
  generalize 2^(2*N+1)=p
  generalize 4^(N+1)=w
  generalize sourceZeta N A=z
  generalize eulerBound N A=v
  generalize z^2=zz
  generalize 4^N*zz=prod
  omega
end ThreeSum.WeightedGlobalArenaFrontendResources
