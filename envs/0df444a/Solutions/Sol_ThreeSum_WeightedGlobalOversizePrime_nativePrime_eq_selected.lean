-- Prove2me | solution 1 for ThreeSum.WeightedGlobalOversizePrime.nativePrime_eq_selected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:04:29.716507+00:00
-- url     : https://prove2.me/submissions/8634c361-322c-4291-b04b-31c1a8264a50

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryEntropyRates
import Definitions.Def_Submission_Weighted_Global_TernaryCoverCapParameters
import Definitions.Def_Submission_Weighted_Global_TernaryOversizePrime

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalOversizePrime
open Finset WeightedGlobalCoverScale WeightedGlobalEntropyRates WeightedGlobalLocalParameters
open TernaryCoverLocal WeightedGlobalCoverFrequency WeightedGlobalCoverCapParameters
set_option maxHeartbeats 2000000
attribute [local semireducible] nativePrime

namespace ThreeSum.WeightedGlobalOversizePrime
theorem _root_.solution (K m : ℕ) :
    nativePrime K m=LocalCoverBounds.selectedPrime (inflatedThreshold K m) :=
  (nativePrimeData K m).property.2
end ThreeSum.WeightedGlobalOversizePrime
