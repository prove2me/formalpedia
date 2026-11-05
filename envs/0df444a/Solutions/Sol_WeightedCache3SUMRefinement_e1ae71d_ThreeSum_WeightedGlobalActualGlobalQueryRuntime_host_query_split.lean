-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalActualGlobalQueryRuntime.host_query_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:56:16.955694+00:00
-- url     : https://prove2.me/submissions/b0bfc55a-42e0-4173-9ed9-b3478a7ba29a

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryActualColoredRuntime
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryUniformQueryTime
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryActualGlobalQueryRuntime

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
theorem _root_.solution {K k m F j : ℕ}
    (maps : Fin F→Weight m (nativePrime K m)) (Q : WeightedGlobalGoodOutputCatalog.Output m) (I : Input) :
    (nativeHost (K:=K) (k:=k) j maps Q I).runtime=
      (nativeHost (K:=K) (k:=k) j maps Q (zeroInput I)).runtime+
        (nativeHost (K:=K) (k:=k) j maps Q I).front.count*I.queryTime:=by
  let H:=nativeHost (K:=K) (k:=k) j maps Q I
  let Z:=nativeHost (K:=K) (k:=k) j maps Q (zeroInput I)
  have hL : H.left=Z.left:=rfl
  have hR : H.right=Z.right:=rfl
  have hfront : H.front.runtime=Z.front.runtime+H.front.count*I.queryTime:=by
    change LightWeightedCountFrontend.time H.front.groups (N m j) H.front.f.L H.front.f.nb H.front.count I.queryTime=
      LightWeightedCountFrontend.time H.front.groups (N m j) H.front.f.L H.front.f.nb H.front.count 0+H.front.count*I.queryTime
    unfold LightWeightedCountFrontend.time LightWeightedWantedRows.time LightWeightedWantedRowDispatch.time
    ring
  change H.runtime=Z.runtime+H.front.count*I.queryTime
  unfold WeightedSourceCountExecutionFactory.Setup.runtime LightWeightedSourceCountHost.time
  rw [hL,hR,hfront]
  ring
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalActualGlobalQueryRuntime
