-- Prove2me | solution 1 for ThreeSum.WeightedGlobalActualColoredRuntime.PB
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T01:03:51.81161+00:00
-- url     : https://prove2.me/submissions/87ebf5fb-90d2-4353-ab8d-3dd636316c1c

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryActualRuntimeParameters
import Definitions.Def_Submission_Weighted_Global_LightTernaryColorPreparationProof
import Definitions.Def_Submission_Weighted_Global_LightTernaryPreparedPostSelection
import Definitions.Def_Submission_Weighted_Global_TernaryFastProgramBudget
import Definitions.Def_Submission_Weighted_Global_TernaryActualCleanupRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryActualColoredRuntime
import Theorems.Thm_ThreeSum_WeightedGlobalActualColoredRuntime_envelope_powerBound
import Theorems.Thm_ThreeSum_WeightedGlobalActualColoredRuntime_preparation_powerBound
import Theorems.Thm_ThreeSum_WeightedGlobalActualColoredRuntime_coefficient_nonneg
import Theorems.Thm_ThreeSum_LightBandRawAResources_envelope_powerBound
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_envelope_powerBound
import Definitions.Def_WeightedCache3SUM_Alias_851b6603dbe122fe
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_const
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_mono_exponent
import Theorems.Thm_ThreeSum_ThreeSumParameterResources_envelope_powerBound
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPairMass_envelope_powerBound


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalActualColoredRuntime
open Light Real Filter StageBounds ArithmeticStageBounds
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalNativeCompleteFrontend
open WeightedGlobalActualPrefixRuntime WeightedGlobalActualSeedRuntime WeightedGlobalEntropyRates
open WeightedGlobalOversizePrime WeightedGlobalOversizeRates WeightedGlobalOversizeOverhead WeightedGlobalCoverScale
open scoped Topology BigOperators
set_option maxHeartbeats 10000000
set_option maxRecDepth 24000
attribute [local instance] Classical.propDecidable
namespace ThreeSum.WeightedGlobalActualColoredRuntime
theorem _root_.solution {K k c d m F D E κ B H β : ℕ} {δ : ℝ}
    (hm : 0<m) (hβ : 1<β) (hδ : 0≤δ)
    (hcarry : WeightedGlobalSignedPadding.carryExponent m β (κ:ℝ)<δ)
    (hroom : WeightedGlobalCountFrontendBudget.frontendExponent+δ≤exponent) :
    PowerBound (uniformTime K k c d m F D E κ B H β) exponent:=by
  have he:=envelope_powerBound hm hβ hδ hcarry
    (coefficient K k c d m F D E κ B H) (coefficient_nonneg _ _ _ _ _ _ _ _ _ _ _)
    (seedPolynomialD K (nativePrime K m) B+6)
  have hp:=(preparation_powerBound hm hβ hδ hcarry).mono_exponent
    (show (1:ℝ)+δ≤exponent by
      have hh : (1:ℝ)≤WeightedGlobalCountFrontendBudget.frontendExponent:=by norm_num [WeightedGlobalCountFrontendBudget.frontendExponent]
      linarith)
  have hzero : (0:ℝ)≤exponent:=by norm_num [exponent]
  exact (((hp.add_same ((PowerBound.const (LightWeightedGlobalArenaTemplate.time E)).mono_exponent hzero)).add_same
    ((PowerBound.const (LightTernaryInitialBudgets.time K)).mono_exponent hzero)).add_same
      (he.mono_exponent hroom)).add_same ((PowerBound.const 10000).mono_exponent hzero)
end ThreeSum.WeightedGlobalActualColoredRuntime
