-- Prove2me | solution 1 for ThreeSum.WeightedGlobalActualColoredRuntime.selected_room
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T23:53:55.080169+00:00
-- url     : https://prove2.me/submissions/8e72835f-6747-4971-8d67-5589187f60d4

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryActualRuntimeParameters
import Definitions.Def_Submission_Weighted_Global_LightTernaryColorPreparationProof
import Definitions.Def_Submission_Weighted_Global_LightTernaryPreparedPostSelection
import Definitions.Def_Submission_Weighted_Global_TernaryFastProgramBudget
import Definitions.Def_Submission_Weighted_Global_TernaryActualCleanupRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryActualColoredRuntime

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
theorem _root_.solution {K : ℕ} (hK : 100000000000000000000≤K) :
    WeightedGlobalCountFrontendBudget.frontendExponent+microAllowance K<exponent:=by
  have hk : (100000000000000000000:ℝ)≤K:=by exact_mod_cast hK
  have hp : (0:ℝ)<K:=by linarith
  have hμ : microAllowance K<(1/1250000000:ℝ):=by
    unfold microAllowance
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith
  norm_num [WeightedGlobalCountFrontendBudget.frontendExponent,exponent]
  linarith
end ThreeSum.WeightedGlobalActualColoredRuntime
