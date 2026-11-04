-- Prove2me | solution 1 for ThreeSum.WeightedGlobalPairedCollisionRate.charge_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:55:19.609955+00:00
-- url     : https://prove2.me/submissions/d733cb58-143d-4fc4-8ab1-bdb1dc122f44

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryPairedFamilyMargin
import Definitions.Def_Submission_ThreeSum_TernaryPairedRecurrence
import Definitions.Def_Submission_Weighted_Global_TernaryPairedCollisionRate
import Theorems.Thm_ThreeSum_WeightedGlobalEntropyRates_actual_output_rate
import Theorems.Thm_ThreeSum_WeightedGlobalOversizeRates_denominator_atTop
import Theorems.Thm_ThreeSum_WeightedGlobalOversizeRates_native_rate_tendsto
import Theorems.Thm_ThreeSum_WeightedGlobalParameters_Hpi_pos


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalPairedCollisionRate
open Filter Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalOversizeRates WeightedGlobalOversizePrime
open WeightedGlobalCoverScale WeightedGlobalLocalParameters
open scoped Topology
set_option maxHeartbeats 1000000
namespace ThreeSum.WeightedGlobalPairedCollisionRate
theorem _root_.solution {K : ℕ} (hK : 0<K) :
    Tendsto (charge K) atTop (𝓝 (1-partitionEntropy/Hpi-2/(K : ℝ))) := by
  have hc := denominator_atTop.const_div_atTop (Real.log 9)
  have h := (((native_rate_tendsto hK).sub hc).const_mul 2).div actual_output_rate Hpi_pos.ne'
  convert h.const_sub 2 using 1
  · rfl
  · have hk : (0 : ℝ)<K := by exact_mod_cast hK
    field_simp [Hpi_pos.ne',hk.ne']
    ring
end ThreeSum.WeightedGlobalPairedCollisionRate
