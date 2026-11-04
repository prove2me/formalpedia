-- Prove2me | solution 1 for ThreeSum.WeightedGlobalActualGlobalQueryRuntime.query_le_cap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T00:00:07.173487+00:00
-- url     : https://prove2.me/submissions/1a7dc183-322d-4862-b501-6beac743c949

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryActualColoredRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryUniformQueryTime
import Definitions.Def_Submission_Weighted_Global_TernaryActualGlobalQueryRuntime
import Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_KeepInputs_trans


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
theorem _root_.solution {K m : ℕ} (S : State K m) (n j : ℕ) (hj : j≤radixLength m n) :
    (S.phase j).queryTime≤queryCap S n:=by
  exact (Finset.le_sup (f:=fun j=>(S.phase j).queryTime) (Finset.mem_range.mpr (by omega))).trans (Nat.le_max_left _ _)
end ThreeSum.WeightedGlobalActualGlobalQueryRuntime
