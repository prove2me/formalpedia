-- Prove2me | solution 1 for ThreeSum.WeightedGlobalOversizeRates.incidence_charge_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:27:21.742345+00:00
-- url     : https://prove2.me/submissions/46761de5-0c42-4589-b61a-3caf80d0853c

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
    Tendsto (incidenceCharge K) atTop (𝓝 (2-partitionEntropy/Hpi+10/K)) := by
  have h := (((native_rate_tendsto hK).sub_const partitionEntropy).const_mul 2).div actual_output_rate Hpi_pos.ne'
  have hh := (h.const_add 1).add (family_charge_tendsto hK)
  convert hh using 1
  · rfl
  · field_simp [Hpi_pos.ne'] <;> ring
end ThreeSum.WeightedGlobalOversizeRates
