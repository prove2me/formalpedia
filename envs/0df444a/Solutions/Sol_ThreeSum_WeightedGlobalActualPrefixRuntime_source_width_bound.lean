-- Prove2me | solution 1 for ThreeSum.WeightedGlobalActualPrefixRuntime.source_width_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T17:02:06.384259+00:00
-- url     : https://prove2.me/submissions/1193263a-1cfe-4dff-9500-b398aa5e5f5a

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_LightTernarySourceHostBudget
import Definitions.Def_Submission_ThreeSum_TernaryWantedDictionaryFiber
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryTime
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeDimensions
import Definitions.Def_Submission_Weighted_Global_TernaryMomentReporterBudget
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedControllerBudget
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedScoreFactory
import Definitions.Def_Submission_Weighted_Global_TernarySignedPreparationBudget
import Definitions.Def_Submission_Weighted_Global_TernaryExtensionBudget
import Definitions.Def_Submission_Weighted_Global_TernaryActualPrefixRuntime

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalActualPrefixRuntime
open Light Real Filter Asymptotics
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalNativeCompleteFrontend
open WeightedGlobalEntropyRates WeightedGlobalDimensionBounds WeightedGlobalOversizePrime
open WeightedGlobalOversizeRates WeightedGlobalOversizeOverhead WeightedGlobalCoverScale
open scoped BigOperators Topology
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
attribute [local instance] Classical.propDecidable
namespace ThreeSum.WeightedGlobalActualPrefixRuntime
theorem _root_.solution (p m r : ℕ) :
    sourceWidth r (2*N m r) (p*(p+1)^r) (p^r)≤
      (2*fixedLength m+3*p+6)*(r+1) :=by
  have hp : p≤2^p:=Nat.lt_two_pow_self.le
  have hps : p+1≤2^(p+1):=Nat.lt_two_pow_self.le
  have hu : p*(p+1)^r+1≤2^(p+(p+1)*r+1) :=by
    have hh:=Nat.mul_le_mul hp (Nat.pow_le_pow_left hps r)
    rw [←pow_mul,←pow_add] at hh
    have h1 : 1≤2^(p+(p+1)*r):=Nat.one_le_pow _ _ (by decide)
    rw [pow_succ]
    omega
  have hm : p^r+1≤2^(p*r+1) :=by
    have hh:=Nat.pow_le_pow_left hp r
    rw [←pow_mul] at hh
    have h1 : 1≤2^(p*r):=Nat.one_le_pow _ _ (by decide)
    rw [pow_succ]
    omega
  have hlu:=Nat.log_mono_right (b:=2) hu
  have hlm:=Nat.log_mono_right (b:=2) hm
  rw [Nat.log_pow (by decide : 1<(2:ℕ))] at hlu hlm
  unfold sourceWidth N
  nlinarith only [hlu,hlm]
end ThreeSum.WeightedGlobalActualPrefixRuntime
