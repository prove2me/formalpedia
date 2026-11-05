-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalActualGlobalQueryRuntime.seed_max_query_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:21:57.863197+00:00
-- url     : https://prove2.me/submissions/be46f60b-69b3-4e0c-9b1e-934d12d387a0

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryActualColoredRuntime
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryUniformQueryTime
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryActualGlobalQueryRuntime
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalActualGlobalQueryRuntime_query_le_cap
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalActualGlobalQueryRuntime_seed_query_split
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalActualGlobalQueryRuntime_wanted_count_le_cap
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSourceCountSeed_seed
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSourceSeed_seed


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalActualGlobalQueryRuntime
open Light Real Filter StageBounds
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalNativeCompleteFrontend
open WeightedGlobalActualPrefixRuntime WeightedGlobalActualSeedRuntime WeightedGlobalActualColoredRuntime
open WeightedGlobalOversizePrime WeightedGlobalOversizeRates WeightedGlobalOversizeOverhead WeightedGlobalCoverScale WeightedGlobalEntropyRates
open scoped Topology BigOperators
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
attribute [local instance] Classical.propDecidable
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalActualGlobalQueryRuntime
theorem _root_.solution {K k m F n j : ℕ}
    (maps : Fin F→Weight m (nativePrime K m)) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (S : State K m) (hF : 0<F) (hj : j≤radixLength m n)
    (hrequest : (S.phase j).requesterCount≤n*2^S.arena.J) :
    prefixSeedTime (K:=K) (k:=k) maps Q (S.phase j) S.arena (S.seeds j)≤
      prefixSeedTime (K:=K) (k:=k) maps Q ((zeroState S).phase j) S.arena ((zeroState S).seeds j)+
        (S.arena.J+2)^4*wantedCap K k m F n S.arena.J*queryCap S n:=by
  unfold prefixSeedTime
  apply Finset.sup_le
  intro seed hseed
  have hs:=seed_query_split (k:=k) (j:=j) maps Q (S.phase j) S.arena (S.seeds j seed)
  have hc:=wanted_count_le_cap (k:=k) (j:=j) maps (sourceInput (S.phase j) S.arena seed (S.seeds j seed)) hF hj hrequest
  have ht:=query_le_cap S n j hj
  have hmul:=Nat.mul_le_mul (Nat.mul_le_mul_left ((S.arena.J+2)^4) hc) ht
  have hzero:=Finset.le_sup (f:=fun seed=>LightWeightedGlobalSeedScoreFactory.runtime (S.seeds j seed)
    (nativeHost (K:=K) (k:=k) j maps Q (sourceInput (zeroInput (S.phase j)) S.arena seed (S.seeds j seed))) K
      (4^fixedLength m) F (outputCap K k m F) ((nativePrime K m)*(nativePrime K m+1)^j)
      (WeightedGlobalGoodOutputCatalog.raws maps (threshold K k m))
      (WeightedGlobalGoodOutputCatalog.wordCodes maps (threshold K k m))
      (WeightedGlobalGoodOutputCatalog.mapCodes maps (threshold K k m))) hseed
  change _≤_ at hc
  rw [hs]
  exact Nat.add_le_add hzero hmul
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalActualGlobalQueryRuntime
