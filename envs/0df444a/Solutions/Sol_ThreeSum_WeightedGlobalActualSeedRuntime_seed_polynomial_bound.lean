-- Prove2me | solution 1 for ThreeSum.WeightedGlobalActualSeedRuntime.seed_polynomial_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T23:19:56.884196+00:00
-- url     : https://prove2.me/submissions/f9612ffc-e87a-4d7f-981e-a7120d396466

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryActualPrefixRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaControllerCore
import Definitions.Def_Submission_Weighted_Global_TernarySeedCoefficientBudget
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixStep
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixInit
import Definitions.Def_Submission_Weighted_Global_TernaryActualSeedRuntime
import Theorems.Thm_ThreeSum_WeightedGlobalSeedCoefficientBudget_seed_coefficient_polynomial


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalActualSeedRuntime
open Real Light Filter
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalNativeCompleteFrontend
open WeightedGlobalActualPrefixRuntime WeightedGlobalEntropyRates WeightedGlobalOversizePrime
open WeightedGlobalOversizeRates WeightedGlobalOversizeOverhead WeightedGlobalCoverScale
set_option maxHeartbeats 10000000
set_option maxRecDepth 24000
attribute [local instance] Classical.propDecidable
namespace ThreeSum.WeightedGlobalActualSeedRuntime
theorem _root_.solution (K p B J j : ℕ) (hj : j≤J) :
    seedCoefficient K J p B (p*(p+1)^j) j≤seedPolynomialC K p B*(J+1)^seedPolynomialD K p B:=
  Classical.choose_spec (Classical.choose_spec
    (WeightedGlobalSeedCoefficientBudget.seed_coefficient_polynomial K p B p)) J j hj
end ThreeSum.WeightedGlobalActualSeedRuntime
