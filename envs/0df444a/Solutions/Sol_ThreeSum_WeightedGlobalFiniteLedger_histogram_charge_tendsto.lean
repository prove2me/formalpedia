-- Prove2me | solution 1 for ThreeSum.WeightedGlobalFiniteLedger.histogram_charge_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:53:42.545669+00:00
-- url     : https://prove2.me/submissions/d4c63d40-8792-4cdd-a65f-b929037f6263

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
    Tendsto histogramCharge atTop (𝓝 (1+partitionEntropy/Hpi)) := by
  have h := (actual_prime_rate.const_mul 2).div actual_output_rate Hpi_pos.ne'
  convert h using 1
  · rfl
  · field_simp [Hpi_pos.ne']
end ThreeSum.WeightedGlobalFiniteLedger
