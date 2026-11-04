-- Prove2me | solution 1 for ThreeSum.WeightedGlobalActualSeedRuntime.prefixSeedTime_eq_core
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T23:24:38.149954+00:00
-- url     : https://prove2.me/submissions/483829f4-c802-410d-bf1d-3402e7d40c76

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryActualPrefixRuntime
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaControllerCore
import Definitions.Def_Submission_Weighted_Global_TernarySeedCoefficientBudget
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixStep
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixInit
import Definitions.Def_Submission_Weighted_Global_TernaryActualSeedRuntime
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceCountSeed_seed
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceSeed_seed


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
theorem _root_.solution {K k m F j : ℕ}
    (maps : Fin F→Weight m (nativePrime K m)) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (I : Input) (A : Inputs)
    (D : (seed : ℕ)→LightWeightedGlobalSeedScoreFactory.Data (config (nativePrime K m) j I A seed))
    (U : ℕ) (L R : ℕ→ℕ→ℤ) :
    prefixSeedTime (K:=K) (k:=k) maps Q I A D=
      WeightedGlobalArenaControllerCore.seedTime
        (WeightedGlobalArenaControllerCore.family maps (threshold K k m)
          (WeightedGlobalCoverCapParameters.sourceCap m (nativePrime K m)) U Q I A D L R)
        K (4^fixedLength m) F (menuSize K m A.J*menuSize K m A.J)
        (WeightedGlobalGoodOutputCatalog.raws maps (threshold K k m))
        (WeightedGlobalGoodOutputCatalog.wordCodes maps (threshold K k m))
        (WeightedGlobalGoodOutputCatalog.mapCodes maps (threshold K k m)):=rfl
end ThreeSum.WeightedGlobalActualSeedRuntime
