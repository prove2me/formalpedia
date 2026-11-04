-- Prove2me | solution 1 for ThreeSum.WeightedGlobalActualGlobalQueryRuntime.correction_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T23:59:41.382069+00:00
-- url     : https://prove2.me/submissions/9a8b1d3b-e845-4e5c-8ed9-f539a652ee41

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryActualColoredRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryUniformQueryTime
import Definitions.Def_Submission_Weighted_Global_TernaryActualGlobalQueryRuntime
import Theorems.Thm_ThreeSum_WeightedGlobalActualSeedRuntime_menu_square_bound


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
theorem _root_.solution {K k m F n Hdet : ℕ} (S : State K m)
    (hJ : radixLength m n≤S.arena.J) :
    totalCorrection k F Hdet S n≤
      (16*menuCoefficient K (nativePrime K m)+(TernaryMomentSchedule.channels (2*Hdet+1)).length)*
        (S.arena.J+1)^7*(wantedCap K k m F n S.arena.J*queryCap S n):=by
  have hmenu:=menu_square_bound K m S.arena.J
  have hcoord : (S.arena.J+2)^4≤16*(S.arena.J+1)^4:=by nlinarith only [Nat.pow_le_pow_left (show S.arena.J+2≤2*(S.arena.J+1) by omega) 4]
  have hmult:=Nat.mul_le_mul (Nat.mul_le_mul hJ hmenu) hcoord
  have hmain : radixLength m n*(menuSize K m S.arena.J*menuSize K m S.arena.J+1)*(S.arena.J+2)^4≤
      16*menuCoefficient K (nativePrime K m)*(S.arena.J+1)^7:=by
    have hh : S.arena.J≤S.arena.J+1:=by omega
    have hh':=Nat.mul_le_mul_right (menuCoefficient K (nativePrime K m)*(S.arena.J+1)^2*(16*(S.arena.J+1)^4)) hh
    nlinarith only [hmult,hh']
  have hm:=Nat.mul_le_mul_right (wantedCap K k m F n S.arena.J*queryCap S n) hmain
  have hpow : 1≤(S.arena.J+1)^7:=Nat.one_le_pow _ _ (by omega)
  have ha:=Nat.mul_le_mul_right
    ((TernaryMomentSchedule.channels (2*Hdet+1)).length*(wantedCap K k m F n S.arena.J*queryCap S n)) hpow
  unfold totalCorrection prefixCorrection
  nlinarith only [hm,ha]
end ThreeSum.WeightedGlobalActualGlobalQueryRuntime
