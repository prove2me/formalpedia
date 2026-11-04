-- Prove2me | solution 1 for ThreeSum.WeightedGlobalOversizeDimensions.partition_le_native
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:08:17.557229+00:00
-- url     : https://prove2.me/submissions/c64a3a6f-36aa-4a4e-a49d-23e5a91bbdc7

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeOverhead
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeDimensions
import Theorems.Thm_ThreeSum_TernaryTypeLowerBound_partition_cap_le_prime
import Theorems.Thm_ThreeSum_WeightedGlobalLocalParameters_fixedPi_space
import Theorems.Thm_ThreeSum_WeightedGlobalLocalParameters_fixedPi_total
import Theorems.Thm_ThreeSum_WeightedGlobalOversizePrime_nativePrime_base_lower
import Theorems.Thm_ThreeSum_WeightedSchedule_fixedPi_total


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalOversizeDimensions
open Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open WeightedGlobalLocalParameters WeightedGlobalOversizePrime WeightedGlobalOversizeRates
open WeightedGlobalPrincipalDimensions WeightedGlobalDimensionBounds TernaryJointType
namespace ThreeSum.WeightedGlobalOversizeDimensions
theorem _root_.solution {K : ℕ} (hK : 0 < K) (m : ℕ) : partitionCap m ≤ nativePrime K m :=
  TernaryTypeLowerBound.partition_cap_le_prime (fixedPi m) (fixedPi_total m) (fixedPi_space m)
    (nativePrime K m) (nativePrime_base_lower hK m)
end ThreeSum.WeightedGlobalOversizeDimensions
