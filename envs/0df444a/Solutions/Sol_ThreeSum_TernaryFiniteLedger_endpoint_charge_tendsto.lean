-- Prove2me | solution 1 for ThreeSum.TernaryFiniteLedger.endpoint_charge_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:33:19.520975+00:00
-- url     : https://prove2.me/submissions/9d4bd8e8-2c1f-47f5-b706-06aedf794142

import Definitions.Def_Submission_ThreeSum_TernaryEntropyRates
import Definitions.Def_Submission_ThreeSum_TernaryDimensionBounds
import Definitions.Def_Submission_ThreeSum_TernaryFiniteLedger
import Theorems.Thm_ThreeSum_TernaryEntropyRates_actual_endpoint_rate
import Theorems.Thm_ThreeSum_TernaryEntropyRates_actual_output_rate
import Theorems.Thm_ThreeSum_TernaryParameters_Hpi_pos


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryFiniteLedger
open Filter Real TernaryParameters TernaryEntropyRates TernaryCoverScale
open scoped Topology
namespace ThreeSum.TernaryFiniteLedger
theorem _root_.solution :
    Tendsto endpointCharge atTop (𝓝 (2*Halpha/Hpi)) :=
  (actual_endpoint_rate.const_mul 2).div actual_output_rate Hpi_pos.ne'
end ThreeSum.TernaryFiniteLedger
