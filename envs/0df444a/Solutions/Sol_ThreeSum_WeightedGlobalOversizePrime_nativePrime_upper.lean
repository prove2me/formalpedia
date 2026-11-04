-- Prove2me | solution 1 for ThreeSum.WeightedGlobalOversizePrime.nativePrime_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:30:29.123237+00:00
-- url     : https://prove2.me/submissions/a162c742-aaf6-41f9-9437-01bcfdb576a2

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryEntropyRates
import Definitions.Def_Submission_Weighted_Global_TernaryCoverCapParameters
import Definitions.Def_Submission_Weighted_Global_TernaryOversizePrime
import Theorems.Thm_ThreeSum_WeightedGlobalOversizePrime_nativePrime_eq_selected
import Theorems.Thm_ThreeSum_WeightedGlobalOversizePrime_inflation_pos
import Theorems.Thm_ThreeSum_LocalCoverBounds_selectedPrime_sq_upper
import Theorems.Thm_ThreeSum_WeightedGlobalCoverScale_threshold_pos


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalOversizePrime
open Finset WeightedGlobalCoverScale WeightedGlobalEntropyRates WeightedGlobalLocalParameters
open TernaryCoverLocal WeightedGlobalCoverFrequency WeightedGlobalCoverCapParameters
set_option maxHeartbeats 2000000
attribute [local semireducible] nativePrime

namespace ThreeSum.WeightedGlobalOversizePrime
theorem _root_.solution {K : ℕ} (hK : 0 < K) (m : ℕ) :
    nativePrime K m^2 ≤ 16*inflatedThreshold K m := by
  rw [nativePrime_eq_selected]
  exact LocalCoverBounds.selectedPrime_sq_upper (Nat.mul_pos (threshold_pos m) (Nat.pow_pos (inflation_pos hK m)))
end ThreeSum.WeightedGlobalOversizePrime
