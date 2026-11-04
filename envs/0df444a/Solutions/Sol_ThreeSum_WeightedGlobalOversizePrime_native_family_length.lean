-- Prove2me | solution 1 for ThreeSum.WeightedGlobalOversizePrime.native_family_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:44:53.524187+00:00
-- url     : https://prove2.me/submissions/93de7495-cc7e-44e0-a2a1-fd5e877c167f

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryEntropyRates
import Definitions.Def_Submission_Weighted_Global_TernaryCoverCapParameters
import Definitions.Def_Submission_Weighted_Global_TernaryOversizePrime
import Theorems.Thm_ThreeSum_Cover_greedyChoices_length


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalOversizePrime
open Finset WeightedGlobalCoverScale WeightedGlobalEntropyRates WeightedGlobalLocalParameters
open TernaryCoverLocal WeightedGlobalCoverFrequency WeightedGlobalCoverCapParameters
set_option maxHeartbeats 2000000

namespace ThreeSum.WeightedGlobalOversizePrime
theorem _root_.solution (K m k : ℕ) :
    (nativeFamily K m k).length=inflatedFrequency K m*(Nat.log2 (nativePrime K m^2)+1) :=
  Cover.greedyChoices_length _ _ _ _
end ThreeSum.WeightedGlobalOversizePrime
