-- Prove2me | solution 1 for ThreeSum.WeightedGlobalOversizeRates.query_charge_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:35:19.029276+00:00
-- url     : https://prove2.me/submissions/0cccf880-5bff-4d13-a358-fd7554472cfe

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
    Tendsto (queryCharge K) atTop (𝓝 (2-partitionEntropy/Hpi+2*queryEntropy/Hpi+10/K)) := by
  have h := ((((native_rate_tendsto hK).sub_const partitionEntropy).add_const queryEntropy).const_mul 2).div actual_output_rate Hpi_pos.ne'
  have hh := (h.const_add 1).add (family_charge_tendsto hK)
  convert hh using 1
  · rfl
  · field_simp [Hpi_pos.ne'] <;> ring
end ThreeSum.WeightedGlobalOversizeRates
