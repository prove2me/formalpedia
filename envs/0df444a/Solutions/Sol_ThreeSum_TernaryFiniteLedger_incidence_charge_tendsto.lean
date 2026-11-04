-- Prove2me | solution 1 for ThreeSum.TernaryFiniteLedger.incidence_charge_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:36:59.229746+00:00
-- url     : https://prove2.me/submissions/00992340-f6fe-4ff4-b6ea-2f73e9237ad5

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
    Tendsto incidenceCharge atTop (𝓝 (2-partitionEntropy/Hpi)) := by
  have h := ((actual_output_rate.sub actual_prime_rate).const_mul 2).div
    actual_output_rate Hpi_pos.ne'
  have hh := h.const_add 1
  convert hh using 1
  · rfl
  · field_simp [Hpi_pos.ne']
    ring
end ThreeSum.TernaryFiniteLedger
