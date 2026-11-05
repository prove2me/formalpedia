-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalSeedCoefficientBudget.hash_linear
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T14:00:24.243203+00:00
-- url     : https://prove2.me/submissions/c446a871-ba52-4c32-9ad5-ecfc5963f0d7

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryActualPrefixRuntime
import Definitions.Def_Submission_ThreeSum_LightTernaryWantedBudget
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySeedCoefficientBudget

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalSeedCoefficientBudget
open WeightedGlobalActualPrefixRuntime
set_option maxHeartbeats 6000000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalSeedCoefficientBudget
theorem _root_.solution (J p B : ℕ) :
    LightSignedRowHash.time (J+2) p B+120≤
      (596+80*p*(p+B))*(J+1) := by
  unfold LightSignedRowHash.time LightReportingAffine.time LightNaturalDot.reducedTime
    LightNaturalDot.time LightBooleanDot.time
  nlinarith [Nat.zero_le (p*(p+B)*J)]
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalSeedCoefficientBudget
