-- Prove2me | solution 1 for ThreeSum.WeightedGlobalSeedCoefficientBudget.hash_linear
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T17:13:28.757216+00:00
-- url     : https://prove2.me/submissions/3b36523d-75a7-4fae-88dc-c5c95438562e

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryActualPrefixRuntime
import Definitions.Def_Submission_ThreeSum_LightTernaryWantedBudget
import Definitions.Def_Submission_Weighted_Global_TernarySeedCoefficientBudget

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalSeedCoefficientBudget
open WeightedGlobalActualPrefixRuntime
set_option maxHeartbeats 6000000
namespace ThreeSum.WeightedGlobalSeedCoefficientBudget
theorem _root_.solution (J p B : ℕ) :
    LightSignedRowHash.time (J+2) p B+120≤
      (596+80*p*(p+B))*(J+1) := by
  unfold LightSignedRowHash.time LightReportingAffine.time LightNaturalDot.reducedTime
    LightNaturalDot.time LightBooleanDot.time
  nlinarith [Nat.zero_le (p*(p+B)*J)]
end ThreeSum.WeightedGlobalSeedCoefficientBudget
