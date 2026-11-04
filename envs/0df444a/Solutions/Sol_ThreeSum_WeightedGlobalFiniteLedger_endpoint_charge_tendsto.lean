-- Prove2me | solution 1 for ThreeSum.WeightedGlobalFiniteLedger.endpoint_charge_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:53:27.499297+00:00
-- url     : https://prove2.me/submissions/f1b0ccad-63e1-4b57-a4eb-0f5f40d07911

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryEntropyRates
import Definitions.Def_Submission_Weighted_Global_DimensionBounds
import Definitions.Def_Submission_Weighted_Global_TernaryFiniteLedger
import Theorems.Thm_ThreeSum_WeightedGlobalEntropyRates_actual_endpoint_rate
import Theorems.Thm_ThreeSum_WeightedGlobalEntropyRates_actual_output_rate
import Theorems.Thm_ThreeSum_WeightedGlobalParameters_Hpi_pos


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalFiniteLedger
open Filter Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open scoped Topology
namespace ThreeSum.WeightedGlobalFiniteLedger
theorem _root_.solution :
    Tendsto endpointCharge atTop (𝓝 (2*Halpha/Hpi)) :=
  (actual_endpoint_rate.const_mul 2).div actual_output_rate Hpi_pos.ne'
end ThreeSum.WeightedGlobalFiniteLedger
