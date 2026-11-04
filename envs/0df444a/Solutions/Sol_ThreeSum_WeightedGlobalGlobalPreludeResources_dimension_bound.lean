-- Prove2me | solution 1 for ThreeSum.WeightedGlobalGlobalPreludeResources.dimension_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:55:33.448748+00:00
-- url     : https://prove2.me/submissions/5ae4107f-2e33-4016-8544-437f0b0a9944

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryGlobalPreludeProof
import Definitions.Def_Submission_Weighted_Global_LightTernaryDimensionsBudget
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
import Definitions.Def_Submission_Weighted_Global_TernaryGlobalPreludeResources
import Theorems.Thm_ThreeSum_LightWeightedGlobalDimensions_word_polynomial


set_option autoImplicit false
open ThreeSum ThreeSum.WeightedGlobalGlobalPreludeResources
open Light LightWeightedGlobalGlobalPrelude
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
namespace ThreeSum.WeightedGlobalGlobalPreludeResources
theorem _root_.solution {M b p K : ℕ} [Fact p.Prime] (hM : 1<M) (hb : 1<b) (κ n : ℕ) :
    LightWeightedGlobalDimensions.word M b p K n (n^κ)≤wordCoefficient M b p K*(n+1)^(κ+2) :=by
  have hn : n^κ≤(n+1)^κ :=Nat.pow_le_pow_left (by omega) _
  have hpos : 1≤(n+1)^κ :=Nat.one_le_pow _ _ (by omega)
  have hh : n^κ+1≤2*(n+1)^κ :=by omega
  calc
    _≤LightWeightedGlobalDimensions.coefficient M b p K*(n+1)^2*(n^κ+1) :=
      LightWeightedGlobalDimensions.word_polynomial hM hb n (n^κ)
    _≤LightWeightedGlobalDimensions.coefficient M b p K*(n+1)^2*(2*(n+1)^κ) :=Nat.mul_le_mul_left _ hh
    _=wordCoefficient M b p K*(n+1)^(κ+2) :=by unfold wordCoefficient; rw [pow_add]; ring
end ThreeSum.WeightedGlobalGlobalPreludeResources
