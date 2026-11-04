-- Prove2me | solution 1 for ThreeSum.WeightedGlobalOversizeRates.soft_certificate_margin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:02:50.927906+00:00
-- url     : https://prove2.me/submissions/8f78fa2d-5eef-4e49-a279-05a2a1e0deaa

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryOversizePrime
import Definitions.Def_Submission_Weighted_Global_TernaryFiniteLedger
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeRates

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalOversizeRates
open Filter Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open WeightedGlobalLocalParameters WeightedGlobalOversizePrime
open scoped Topology
set_option maxHeartbeats 1000000
namespace ThreeSum.WeightedGlobalOversizeRates
theorem _root_.solution : targetExponent-softCertificate=(1/156250000 : ℝ) := by
  norm_num [targetExponent,softCertificate]
end ThreeSum.WeightedGlobalOversizeRates
