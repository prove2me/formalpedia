-- Prove2me | solution 1 for ThreeSum.WeightedGlobalOversizePrime.nativePrime_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:08:23.339513+00:00
-- url     : https://prove2.me/submissions/ecb42e27-7dd3-456f-9856-f318e810ff6f

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryEntropyRates
import Definitions.Def_Submission_Weighted_Global_TernaryCoverCapParameters
import Definitions.Def_Submission_Weighted_Global_TernaryOversizePrime
import Theorems.Thm_ThreeSum_WeightedGlobalOversizePrime_nativePrime_eq_selected
import Theorems.Thm_ThreeSum_LocalCoverBounds_selectedPrime_sq_lower


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalOversizePrime
open Finset WeightedGlobalCoverScale WeightedGlobalEntropyRates WeightedGlobalLocalParameters
open TernaryCoverLocal WeightedGlobalCoverFrequency WeightedGlobalCoverCapParameters
set_option maxHeartbeats 2000000
attribute [local semireducible] nativePrime

namespace ThreeSum.WeightedGlobalOversizePrime
theorem _root_.solution (K m : ℕ) : inflatedThreshold K m ≤ nativePrime K m^2 := by
  rw [nativePrime_eq_selected]
  exact LocalCoverBounds.selectedPrime_sq_lower _
end ThreeSum.WeightedGlobalOversizePrime
