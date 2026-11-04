-- Prove2me | solution 1 for ThreeSum.WeightedGlobalActualGlobalQueryRuntime.wanted_count_le_cap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T00:01:39.345881+00:00
-- url     : https://prove2.me/submissions/95c9d084-c12e-4c9c-becf-3c0cbed1fc90

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryActualColoredRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryUniformQueryTime
import Definitions.Def_Submission_Weighted_Global_TernaryActualGlobalQueryRuntime
import Theorems.Thm_ThreeSum_TernaryCoverCapParameters_rawThreshold_pos
import Theorems.Thm_ThreeSum_WeightedGlobalActualPrefixRuntime_wanted_entries_cap
import Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_KeepInputs_trans
import Theorems.Thm_ThreeSum_WeightedGlobalCoverCapParameters_rawThreshold_pos
import Theorems.Thm_ThreeSum_WeightedGlobalGoodOutputCatalog_cap_pos


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
theorem _root_.solution {K k m F n digitLength j : ℕ}
    (maps : Fin F→Weight m (nativePrime K m)) (I : Input)
    (hF : 0<F) (hj : j≤radixLength m n) (hrequest : I.requesterCount≤n*2^digitLength) :
    (entries (r:=j) maps (threshold K k m) I).length≤wantedCap K k m F n digitLength:=by
  have hpos : 1≤outputCap K k m F:=by
    unfold outputCap
    exact Nat.succ_le_iff.mpr (Nat.mul_pos hF (WeightedGlobalGoodOutputCatalog.cap_pos (WeightedGlobalCoverCapParameters.rawThreshold_pos _ _ _)))
  have hc:=wanted_entries_cap (j:=j) maps (threshold K k m) I
  exact hc.trans (Nat.mul_le_mul hrequest (Nat.pow_le_pow_right hpos hj))
end ThreeSum.WeightedGlobalActualGlobalQueryRuntime
