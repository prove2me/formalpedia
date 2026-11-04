-- Prove2me | solution 1 for ThreeSum.WeightedGlobalGlobalPreludeResources.parameter_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:15:44.334076+00:00
-- url     : https://prove2.me/submissions/e7339978-0e71-490c-b5e9-5b286406c486

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryGlobalPreludeProof
import Definitions.Def_Submission_Weighted_Global_LightTernaryDimensionsBudget
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
import Definitions.Def_Submission_Weighted_Global_TernaryGlobalPreludeResources
import Theorems.Thm_ThreeSum_WeightedGlobalGlobalPreludeResources_dimension_bound

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedGlobalGlobalPreludeResources
open Light LightWeightedGlobalGlobalPrelude
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
namespace ThreeSum.WeightedGlobalGlobalPreludeResources
theorem _root_.solution {M b p K : ℕ} [Fact p.Prime] (hM : 1<M) (hb : 1<b) (κ n : ℕ) :
    LightExtensionBackendLayout.params
      (LightWeightedGlobalDimensions.dim M b p K n (n^κ)) p
      (p^(LightWeightedGlobalDimensions.dim M b p K n (n^κ))) (LightWeightedGlobalDimensions.J M b n (n^κ))≤
        baseCoefficient M b p K*(n+1)^(κ+2) :=by
  have hh:=dimension_bound (p:=p) (K:=K) hM hb κ n
  have hj : LightWeightedGlobalDimensions.J M b n (n^κ)≤LightWeightedGlobalDimensions.word M b p K n (n^κ) :=by unfold LightWeightedGlobalDimensions.word; omega
  have hd : LightWeightedGlobalDimensions.dim M b p K n (n^κ)≤LightWeightedGlobalDimensions.word M b p K n (n^κ) :=by unfold LightWeightedGlobalDimensions.word; omega
  have hq : p^(LightWeightedGlobalDimensions.dim M b p K n (n^κ))≤LightWeightedGlobalDimensions.word M b p K n (n^κ) :=by unfold LightWeightedGlobalDimensions.word; omega
  have hp : 1≤(n+1)^(κ+2) :=Nat.one_le_pow _ _ (by omega)
  unfold LightExtensionBackendLayout.params baseCoefficient
  nlinarith
end ThreeSum.WeightedGlobalGlobalPreludeResources
