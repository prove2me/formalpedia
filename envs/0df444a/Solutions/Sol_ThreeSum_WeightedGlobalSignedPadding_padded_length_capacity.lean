-- Prove2me | solution 1 for ThreeSum.WeightedGlobalSignedPadding.padded_length_capacity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:08:01.865335+00:00
-- url     : https://prove2.me/submissions/790a05cc-3a9f-4263-aa60-b85e1a371e97

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernarySignedReduction
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeOverhead
import Definitions.Def_Submission_Weighted_Global_TernarySignedPadding

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalSignedPadding
open Filter Real TernarySignedReduction WeightedGlobalCoverScale
open WeightedGlobalPrincipalDimensions WeightedGlobalOversizeOverhead WeightedGlobalOversizePrime
open WeightedGlobalEntropyRates WeightedGlobalLocalParameters WeightedGlobalOversizeRates WeightedGlobalParameters
open scoped Topology
namespace ThreeSum.WeightedGlobalSignedPadding
theorem _root_.solution {b : ℕ} (hb : 1<b) (U r : ℕ) :
    4*U<b^paddedLength b U r := by
  have h := Nat.le_pow_clog hb (4*U+1)
  have he : digitLength b U ≤ paddedLength b U r := by unfold paddedLength; omega
  exact lt_of_lt_of_le (lt_of_lt_of_le (by omega : 4*U<4*U+1) h)
    (Nat.pow_le_pow_right hb.le he)
end ThreeSum.WeightedGlobalSignedPadding
