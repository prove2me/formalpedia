-- Prove2me | solution 1 for ThreeSum.WeightedGlobalFiniteLedger.incidence_charge_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:52:26.887313+00:00
-- url     : https://prove2.me/submissions/57c55d77-2a75-4eee-80d8-47db63c8620c

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
    Tendsto incidenceCharge atTop (𝓝 (2-partitionEntropy/Hpi)) := by
  have h := ((actual_output_rate.sub actual_prime_rate).const_mul 2).div
    actual_output_rate Hpi_pos.ne'
  have hh := h.const_add 1
  convert hh using 1
  · rfl
  · field_simp [Hpi_pos.ne']
    ring
end ThreeSum.WeightedGlobalFiniteLedger
