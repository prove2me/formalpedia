-- Prove2me | solution 1 for ThreeSum.WeightedGlobalActualColoredRuntime.coefficient_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T00:32:10.128733+00:00
-- url     : https://prove2.me/submissions/7872138f-9706-4ed4-b419-d26e72c74808

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryActualRuntimeParameters
import Definitions.Def_Submission_Weighted_Global_LightTernaryColorPreparationProof
import Definitions.Def_Submission_Weighted_Global_LightTernaryPreparedPostSelection
import Definitions.Def_Submission_Weighted_Global_TernaryFastProgramBudget
import Definitions.Def_Submission_Weighted_Global_TernaryActualCleanupRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryActualColoredRuntime
import Theorems.Thm_ThreeSum_WeightedGlobalActualColoredRuntime_reporterCoefficient_nonneg
import Theorems.Thm_ThreeSum_WeightedGlobalActualSeedRuntime_prefixConstant_nonneg
import Theorems.Thm_ThreeSum_WeightedGlobalActualSeedRuntime_volumeConstant_nonneg


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
theorem _root_.solution (K k c d m F D E κ B H : ℕ) :
    0≤coefficient K k c d m F D E κ B H:=by
  unfold coefficient postCoefficient
  positivity [prefixConstant_nonneg K k c d m F D E κ B,
    reporterCoefficient_nonneg K k c d m F D E κ B H,volumeConstant_nonneg K k c d m]
end ThreeSum.WeightedGlobalActualColoredRuntime
