-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalActualGlobalQueryRuntime.time_le_uniform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:46:59.986203+00:00
-- url     : https://prove2.me/submissions/29f1a1d7-a899-491c-ac51-44b9dfcd5ec8

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryActualColoredRuntime
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryUniformQueryTime
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryActualGlobalQueryRuntime
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalActualGlobalQueryRuntime_time_query_bound
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalActualGlobalQueryRuntime_correction_bound
import Theorems.Thm_ThreeSum_LightPrimality_time_le_uniform
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalActualColoredRuntime_time_le_uniform
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaScoreScan_KeepInputs_trans


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
theorem _root_.solution {K k b m F β κ n D E B Hdet : ℕ}
    {maps : Fin F→Weight m (nativePrime K m)} {Q : WeightedGlobalGoodOutputCatalog.Output m}
    {S : State K m} (H : Fits (k:=k) maps Q (zeroState S) β κ n D E B)
    (hK : 0<K) (hk : 0<k) (hgood : GoodBlock K m) (hn : 1<n)
    (hFpos : 0<F) (hF : F≤(nativeFamily K m k).length)
    (hb : WeightedGlobalActualPrefixRuntime.localFactor m≤b)
    (hposL : 1≤(localRecords maps (WeightedGlobalCoverCapParameters.sourceCap m (nativePrime K m)) false).length)
    (hposR : 1≤(localRecords maps (WeightedGlobalCoverCapParameters.sourceCap m (nativePrime K m)) true).length)
    (hquery : (queryCap S n:ℝ)≤(WeightedGlobalUniformQueryTime.coefficient m D E κ:ℝ)*
      (S.arena.J+1:ℕ)^3*WeightedGlobalCountFrontendBudget.envelope m (radixLength m n))
    (c d : ℕ) (hpoly : b≤c*(fixedLength m+1)^d)
    (hcharge : fullExponent K k c d m≤WeightedGlobalCountFrontendBudget.frontendExponent) :
    WeightedGlobalActualColoredRuntime.time (k:=k) maps Q S E κ Hdet n≤
      uniformTime K k c d m F D E κ B Hdet β n:=by
  have ht:=time_query_bound (Hdet:=Hdet) maps Q S hFpos H
  have hz:=WeightedGlobalActualColoredRuntime.time_le_uniform (Hdet:=Hdet) H hK hk hgood hn hFpos hF hb hposL hposR c d hpoly hcharge
  have hc:=correction_bound (Hdet:=Hdet) maps Q S H hK hk hgood hn hF hb hquery c d hpoly hcharge
  have hceil : totalCorrection k F Hdet S n≤
      WeightedGlobalActualColoredRuntime.envelope (extraCoefficient K k c d m F D E κ B Hdet) 10 m β κ n:=by
    have hh : (totalCorrection k F Hdet S n:ℝ)≤
        (WeightedGlobalActualColoredRuntime.envelope (extraCoefficient K k c d m F D E κ B Hdet) 10 m β κ n:ℝ):=by
      exact hc.trans (Nat.le_ceil _)
    exact_mod_cast hh
  exact ht.trans (Nat.add_le_add hz hceil)
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalActualGlobalQueryRuntime
