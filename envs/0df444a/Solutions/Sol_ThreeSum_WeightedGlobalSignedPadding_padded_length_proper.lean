-- Prove2me | solution 1 for ThreeSum.WeightedGlobalSignedPadding.padded_length_proper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:09:44.951163+00:00
-- url     : https://prove2.me/submissions/8fd893a1-d09e-4150-885a-e29ae122cc95

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
theorem _root_.solution (b U r : ℕ) : r<paddedLength b U r := by
  unfold paddedLength
  omega
end ThreeSum.WeightedGlobalSignedPadding
