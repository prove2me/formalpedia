-- Prove2me | solution 1 for ThreeSum.WeightedGlobalOversizeRates.histogram_charge_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:19:16.597588+00:00
-- url     : https://prove2.me/submissions/89847d10-360c-4f5a-bd65-f9f8236fab9e

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryOversizePrime
import Definitions.Def_Submission_Weighted_Global_TernaryFiniteLedger
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeRates
import Theorems.Thm_ThreeSum_WeightedGlobalOversizeRates_native_rate_tendsto
import Theorems.Thm_ThreeSum_WeightedGlobalOversizeRates_family_charge_tendsto
import Theorems.Thm_ThreeSum_WeightedGlobalEntropyRates_actual_output_rate
import Theorems.Thm_ThreeSum_WeightedGlobalParameters_Hpi_pos


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalOversizeRates
open Filter Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open WeightedGlobalLocalParameters WeightedGlobalOversizePrime
open scoped Topology
set_option maxHeartbeats 1000000
namespace ThreeSum.WeightedGlobalOversizeRates
theorem _root_.solution {K : ℕ} (hK : 0 < K) :
    Tendsto (histogramCharge K) atTop (𝓝 (1+partitionEntropy/Hpi+10/K)) := by
  have h := ((native_rate_tendsto hK).const_mul 2).div actual_output_rate Hpi_pos.ne'
  have hh := h.add (family_charge_tendsto hK)
  convert hh using 1
  · rfl
  · field_simp [Hpi_pos.ne'] <;> ring
end ThreeSum.WeightedGlobalOversizeRates
