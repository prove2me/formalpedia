-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalGlobalPreludeResources.dimension_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T12:00:10.725395+00:00
-- url     : https://prove2.me/submissions/e725c22e-daa6-4bb7-827f-f88e4bec226a

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryGlobalPreludeProof
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryDimensionsBudget
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryGlobalPreludeResources
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalDimensions_word_polynomial


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalGlobalPreludeResources
open Light LightWeightedGlobalGlobalPrelude
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalGlobalPreludeResources
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
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalGlobalPreludeResources
