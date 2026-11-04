-- Prove2me | solution 1 for ThreeSum.WeightedGlobalActualGlobalQueryRuntime.correction_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T00:49:59.281859+00:00
-- url     : https://prove2.me/submissions/eb5f0e4b-96ed-45a7-a0b5-616035e1ba19

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryActualColoredRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryUniformQueryTime
import Definitions.Def_Submission_Weighted_Global_TernaryActualGlobalQueryRuntime
import Theorems.Thm_ThreeSum_WeightedGlobalActualGlobalQueryRuntime_charged_query_product
import Theorems.Thm_ThreeSum_WeightedGlobalActualGlobalQueryRuntime_correction_polynomial
import Theorems.Thm_ThreeSum_WeightedGlobalActualGlobalQueryRuntime_extraCoefficient_nonneg
import Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_KeepInputs_trans
import Theorems.Thm_ThreeSum_WeightedGlobalSignedPadding_padded_length_proper


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
theorem _root_.solution {K k b m F β κ n D E B Hdet : ℕ}
    (maps : Fin F→Weight m (nativePrime K m)) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (S : State K m) (H : Fits (k:=k) maps Q (zeroState S) β κ n D E B)
    (hK : 0<K) (hk : 0<k) (hgood : GoodBlock K m) (hn : 1<n)
    (hF : F≤(nativeFamily K m k).length) (hb : WeightedGlobalActualPrefixRuntime.localFactor m≤b)
    (hquery : (queryCap S n:ℝ)≤(WeightedGlobalUniformQueryTime.coefficient m D E κ:ℝ)*
      (S.arena.J+1:ℕ)^3*WeightedGlobalCountFrontendBudget.envelope m (radixLength m n))
    (c d : ℕ) (hpoly : b≤c*(fixedLength m+1)^d)
    (hcharge : fullExponent K k c d m≤WeightedGlobalCountFrontendBudget.frontendExponent) :
    (totalCorrection k F Hdet S n:ℝ)≤
      extraCoefficient K k c d m F D E κ B Hdet*(J m β κ n+1:ℕ)^10*
        (2:ℝ)^J m β κ n*(n:ℝ)^WeightedGlobalCountFrontendBudget.frontendExponent:=by
  have hd : S.arena.J=J m β κ n:=H.dimension
  have hJ : radixLength m n≤S.arena.J:=by
    rw [hd]
    exact (WeightedGlobalSignedPadding.padded_length_proper β (n^κ) (radixLength m n)).le
  have hc:=correction_polynomial (k:=k) (F:=F) (Hdet:=Hdet) S hJ
  have hc' : (totalCorrection k F Hdet S n:ℝ)≤
      ((16*menuCoefficient K (nativePrime K m)+(TernaryMomentSchedule.channels (2*Hdet+1)).length:ℕ):ℝ)*
        (S.arena.J+1:ℕ)^7*(wantedCap K k m F n S.arena.J*queryCap S n:ℕ):=by exact_mod_cast hc
  have hp:=charged_query_product maps Q S H hK hk hgood hn hF hb hquery c d hpoly
  have hs:=mul_le_mul_of_nonneg_left hp (show (0:ℝ)≤
      ((16*menuCoefficient K (nativePrime K m)+(TernaryMomentSchedule.channels (2*Hdet+1)).length:ℕ):ℝ)*
        (S.arena.J+1:ℕ)^7 by positivity)
  have hmain : (totalCorrection k F Hdet S n:ℝ)≤
      extraCoefficient K k c d m F D E κ B Hdet*(S.arena.J+1:ℕ)^10*
        (2:ℝ)^S.arena.J*(n:ℝ)^fullExponent K k c d m:=by
    apply (hc'.trans hs).trans_eq
    unfold extraCoefficient
    ring
  have hpow:=Real.rpow_le_rpow_of_exponent_le (show (1:ℝ)≤n by exact_mod_cast hn.le) hcharge
  have hx:=mul_le_mul_of_nonneg_left hpow (show (0:ℝ)≤
    extraCoefficient K k c d m F D E κ B Hdet*(S.arena.J+1:ℕ)^10*(2:ℝ)^S.arena.J by
      positivity [extraCoefficient_nonneg K k c d m F D E κ B Hdet])
  rw [←hd]
  exact hmain.trans hx
end ThreeSum.WeightedGlobalActualGlobalQueryRuntime
