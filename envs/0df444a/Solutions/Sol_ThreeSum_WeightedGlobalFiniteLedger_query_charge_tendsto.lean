-- Prove2me | solution 1 for ThreeSum.WeightedGlobalFiniteLedger.query_charge_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:51:54.229271+00:00
-- url     : https://prove2.me/submissions/590449ef-efce-457e-ba9a-9dc936d48fbe

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryEntropyRates
import Definitions.Def_Submission_Weighted_Global_DimensionBounds
import Definitions.Def_Submission_Weighted_Global_TernaryFiniteLedger
import Theorems.Thm_ThreeSum_WeightedGlobalEntropyRates_actual_output_rate
import Theorems.Thm_ThreeSum_WeightedGlobalEntropyRates_actual_prime_rate
import Theorems.Thm_ThreeSum_WeightedGlobalParameters_Hpi_pos


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalFiniteLedger
open Filter Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open scoped Topology
namespace ThreeSum.WeightedGlobalFiniteLedger
theorem _root_.solution :
    Tendsto queryCharge atTop (𝓝 (2-partitionEntropy/Hpi+2*queryEntropy/Hpi)) := by
  have h := (((actual_output_rate.sub actual_prime_rate).add_const queryEntropy).const_mul 2).div
    actual_output_rate Hpi_pos.ne'
  have hh := h.const_add 1
  convert hh using 1
  · rfl
  · field_simp [Hpi_pos.ne']
    ring
end ThreeSum.WeightedGlobalFiniteLedger
