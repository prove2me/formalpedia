-- Prove2me | solution 1 for ThreeSum.WeightedGlobalActualGlobalQueryRuntime.queryCap_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T00:09:38.856005+00:00
-- url     : https://prove2.me/submissions/b2f5f793-3326-4b0c-8dce-c56e5f7d644c

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
theorem _root_.solution {K m n q : ℕ} (S : State K m)
    (hphase : ∀j≤radixLength m n,(S.phase j).queryTime≤q) (hpost : S.post.queryTime≤q) :
    queryCap S n≤q:=by
  apply max_le _ hpost
  exact Finset.sup_le (fun j hj=>hphase j (by have := Finset.mem_range.mp hj; omega))
end ThreeSum.WeightedGlobalActualGlobalQueryRuntime
