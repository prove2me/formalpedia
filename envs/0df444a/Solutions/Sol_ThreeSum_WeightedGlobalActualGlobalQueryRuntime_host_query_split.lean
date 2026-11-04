-- Prove2me | solution 1 for ThreeSum.WeightedGlobalActualGlobalQueryRuntime.host_query_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T00:06:50.468672+00:00
-- url     : https://prove2.me/submissions/92918f00-29f0-4e01-9576-f323d7771c27

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryActualColoredRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryUniformQueryTime
import Definitions.Def_Submission_Weighted_Global_TernaryActualGlobalQueryRuntime

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalActualGlobalQueryRuntime
open Light Real Filter StageBounds
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalNativeCompleteFrontend
open WeightedGlobalActualPrefixRuntime WeightedGlobalActualSeedRuntime WeightedGlobalActualColoredRuntime
open WeightedGlobalOversizePrime WeightedGlobalOversizeRates WeightedGlobalOversizeOverhead WeightedGlobalCoverScale WeightedGlobalEntropyRates
open scoped Topology BigOperators
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
attribute [local instance] Classical.propDecidable
namespace ThreeSum.WeightedGlobalActualGlobalQueryRuntime
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
end ThreeSum.WeightedGlobalActualGlobalQueryRuntime
