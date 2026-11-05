-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPairedCollisionRate.charge_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T11:33:26.737404+00:00
-- url     : https://prove2.me/submissions/3dfacca3-fed1-4b20-96de-4d7dfc30c581

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPairedFamilyMargin
import Definitions.Def_Submission_ThreeSum_TernaryPairedRecurrence
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPairedCollisionRate
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalEntropyRates_actual_output_rate
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalOversizeRates_denominator_atTop
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalOversizeRates_native_rate_tendsto
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalParameters_Hpi_pos


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPairedCollisionRate
open Filter Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalOversizeRates WeightedGlobalOversizePrime
open WeightedGlobalCoverScale WeightedGlobalLocalParameters
open scoped Topology
set_option maxHeartbeats 1000000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPairedCollisionRate
theorem _root_.solution {K : ℕ} (hK : 0<K) :
    Tendsto (charge K) atTop (𝓝 (1-partitionEntropy/Hpi-2/(K : ℝ))) := by
  have hc := denominator_atTop.const_div_atTop (Real.log 9)
  have h := (((native_rate_tendsto hK).sub hc).const_mul 2).div actual_output_rate Hpi_pos.ne'
  convert h.const_sub 2 using 1
  · rfl
  · have hk : (0 : ℝ)<K := by exact_mod_cast hK
    field_simp [Hpi_pos.ne',hk.ne']
    ring
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPairedCollisionRate
