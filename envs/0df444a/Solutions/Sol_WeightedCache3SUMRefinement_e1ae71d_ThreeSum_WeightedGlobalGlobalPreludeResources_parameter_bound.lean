-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalGlobalPreludeResources.parameter_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T12:07:51.842812+00:00
-- url     : https://prove2.me/submissions/dae2c163-d7c6-4cab-b32d-c0556c027ac2

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryGlobalPreludeProof
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryDimensionsBudget
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryGlobalPreludeResources
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalGlobalPreludeResources_dimension_bound

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalGlobalPreludeResources
open Light LightWeightedGlobalGlobalPrelude
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalGlobalPreludeResources
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
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalGlobalPreludeResources
