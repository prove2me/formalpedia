-- Prove2me | solution 1 for ThreeSum.WeightedGlobalActualGlobalQueryRuntime.PB
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T01:35:18.453438+00:00
-- url     : https://prove2.me/submissions/2c978b6e-76e4-4df5-98b8-974863c8ac26

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryActualColoredRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryUniformQueryTime
import Definitions.Def_Submission_Weighted_Global_TernaryActualGlobalQueryRuntime
import Theorems.Thm_ThreeSum_WeightedGlobalActualGlobalQueryRuntime_extraCoefficient_nonneg
import Theorems.Thm_ThreeSum_LightBandRawAResources_envelope_powerBound
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_envelope_powerBound
import Definitions.Def_WeightedCache3SUM_Alias_851b6603dbe122fe
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_mono_exponent
import Theorems.Thm_ThreeSum_ThreeSumParameterResources_envelope_powerBound
import Theorems.Thm_ThreeSum_WeightedGlobalActualColoredRuntime_PB
import Theorems.Thm_ThreeSum_WeightedGlobalActualColoredRuntime_envelope_powerBound
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPairMass_envelope_powerBound


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
theorem _root_.solution {K k c d m F D E κ B H β : ℕ} {δ : ℝ}
    (hm : 0<m) (hβ : 1<β) (hδ : 0≤δ)
    (hcarry : WeightedGlobalSignedPadding.carryExponent m β (κ:ℝ)<δ)
    (hroom : WeightedGlobalCountFrontendBudget.frontendExponent+δ≤WeightedGlobalActualColoredRuntime.exponent) :
    PowerBound (uniformTime K k c d m F D E κ B H β) WeightedGlobalActualColoredRuntime.exponent:=by
  have he:=WeightedGlobalActualColoredRuntime.envelope_powerBound hm hβ hδ hcarry
    (extraCoefficient K k c d m F D E κ B H)
    (extraCoefficient_nonneg K k c d m F D E κ B H) 10
  exact (WeightedGlobalActualColoredRuntime.PB hm hβ hδ hcarry hroom).add_same (he.mono_exponent hroom)
end ThreeSum.WeightedGlobalActualGlobalQueryRuntime
