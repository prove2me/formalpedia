-- Prove2me | solution 1 for ThreeSum.WeightedGlobalActualPrefixRuntime.full_exponent_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T17:09:23.188619+00:00
-- url     : https://prove2.me/submissions/f9527aa5-96b1-4894-b012-abdd3fa66797

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
theorem _root_.solution {K m : ℕ} (hK : 100000000000000000000≤K) (c d : ℕ)
    (hgood : GoodBlock K m)
    (hover : overheadCharge (selectedMoment K) c d m<microAllowance K) :
    fullExponent K (selectedMoment K) c d m<WeightedGlobalCountFrontendBudget.frontendExponent :=by
  have hmax : fullCharge K m<softCertificate:=by
    unfold fullCharge
    exact max_lt (by norm_num [softCertificate])
      (max_lt hgood.2.1 (max_lt hgood.2.2.1
        (max_lt hgood.2.2.2.1 (max_lt hgood.2.2.2.2.1 hgood.2.2.2.2.2))))
  have hkr : (100000000000000000000:ℝ)≤K:=by exact_mod_cast hK
  have hkp : (0:ℝ)<K:=by linarith
  have hmicro : microAllowance K<(1/1250000000:ℝ):=by
    unfold microAllowance
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith
  have hbound : softCertificate+microAllowance K<WeightedGlobalCountFrontendBudget.frontendExponent :=by
    norm_num [softCertificate,WeightedGlobalCountFrontendBudget.frontendExponent]
    linarith
  exact (add_lt_add hmax hover).trans hbound
end ThreeSum.WeightedGlobalActualPrefixRuntime
