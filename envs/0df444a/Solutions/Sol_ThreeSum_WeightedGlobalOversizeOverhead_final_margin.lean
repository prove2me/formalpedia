-- Prove2me | solution 1 for ThreeSum.WeightedGlobalOversizeOverhead.final_margin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:04:57.441734+00:00
-- url     : https://prove2.me/submissions/219670a1-9b40-44cb-a9b3-77bfea63bfdb

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeRates
import Definitions.Def_Submission_Weighted_Global_TernaryRadixOverhead
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeOverhead

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalOversizeOverhead
open Filter Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open WeightedGlobalLocalParameters TernaryCoverLocal WeightedGlobalOversizePrime WeightedGlobalOversizeRates
open WeightedGlobalCoverFrequency WeightedGlobalCoverCapParameters
open scoped Topology
set_option maxHeartbeats 1000000
namespace ThreeSum.WeightedGlobalOversizeOverhead
theorem _root_.solution {K : ℕ} (hK : 100000000000000000000 ≤ K) :
    softCertificate+microAllowance K < targetExponent := by
  have hk : (100000000000000000000 : ℝ) ≤ K := by exact_mod_cast hK
  have hp : (0 : ℝ) < K := by linarith
  have hδ : microAllowance K < (1/1250000000 : ℝ) := by
    unfold microAllowance
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith
  norm_num [softCertificate,targetExponent] at *
  linarith
end ThreeSum.WeightedGlobalOversizeOverhead
