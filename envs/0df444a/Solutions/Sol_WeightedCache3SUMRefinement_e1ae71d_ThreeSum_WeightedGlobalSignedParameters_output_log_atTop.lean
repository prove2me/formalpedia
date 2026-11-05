-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalSignedParameters.output_log_atTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T11:21:26.825952+00:00
-- url     : https://prove2.me/submissions/08cc48e3-eabb-417f-baee-710d720e5e2b

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySignedPadding
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySignedParameters
import Theorems.Thm_ThreeSum_Parameters_log_two_pos
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalEntropyRates_actual_output_rate
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalOversizeRates_denominator_atTop
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalParameters_Hpi_pos
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalParameters_log_two_pos


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalSignedParameters
open Filter Real WeightedGlobalSignedPadding WeightedGlobalCoverScale WeightedGlobalOversizeOverhead
open WeightedGlobalOversizePrime WeightedGlobalEntropyRates WeightedGlobalLocalParameters
open WeightedGlobalOversizeRates WeightedGlobalParameters
open scoped Topology
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalSignedParameters
theorem _root_.solution :
    Tendsto (fun m => Real.log (outputSize m : ℝ)) atTop atTop := by
  have h := denominator_atTop.atTop_mul_pos Hpi_pos actual_output_rate
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
  unfold outputRate
  have hlen : (fixedLength m : ℝ)≠0 := by
    have hp : 0<fixedLength m := by unfold fixedLength; positivity
    exact_mod_cast hp.ne'
  field_simp [hlen,log_two_pos.ne']
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalSignedParameters
