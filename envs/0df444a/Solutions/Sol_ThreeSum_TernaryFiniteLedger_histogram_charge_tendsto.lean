-- Prove2me | solution 1 for ThreeSum.TernaryFiniteLedger.histogram_charge_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:36:57.989203+00:00
-- url     : https://prove2.me/submissions/c20426a1-5301-44ec-bb15-351cd36106b5

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
    Tendsto histogramCharge atTop (𝓝 (1+partitionEntropy/Hpi)) := by
  have h := (actual_prime_rate.const_mul 2).div actual_output_rate Hpi_pos.ne'
  convert h using 1
  · rfl
  · field_simp [Hpi_pos.ne']
end ThreeSum.TernaryFiniteLedger
