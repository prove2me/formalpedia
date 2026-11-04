-- Prove2me | solution 1 for ThreeSum.TernaryFiniteLedger.query_charge_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:36:56.816473+00:00
-- url     : https://prove2.me/submissions/1e05a4a2-48b6-43e0-9e9a-498a8e14d29a

import Definitions.Def_Submission_ThreeSum_TernaryEntropyRates
import Definitions.Def_Submission_ThreeSum_TernaryDimensionBounds
import Definitions.Def_Submission_ThreeSum_TernaryFiniteLedger
import Theorems.Thm_ThreeSum_TernaryEntropyRates_actual_output_rate
import Theorems.Thm_ThreeSum_TernaryEntropyRates_actual_prime_rate
import Theorems.Thm_ThreeSum_TernaryParameters_Hpi_pos


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryFiniteLedger
open Filter Real TernaryParameters TernaryEntropyRates TernaryCoverScale
open scoped Topology
namespace ThreeSum.TernaryFiniteLedger
theorem _root_.solution :
    Tendsto queryCharge atTop (𝓝 (2-partitionEntropy/Hpi+2*queryEntropy/Hpi)) := by
  have h := (((actual_output_rate.sub actual_prime_rate).add_const queryEntropy).const_mul 2).div
    actual_output_rate Hpi_pos.ne'
  have hh := h.const_add 1
  convert hh using 1
  · rfl
  · field_simp [Hpi_pos.ne']
    ring
end ThreeSum.TernaryFiniteLedger
