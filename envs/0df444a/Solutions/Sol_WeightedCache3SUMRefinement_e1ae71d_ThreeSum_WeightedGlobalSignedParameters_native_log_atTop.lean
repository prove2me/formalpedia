-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalSignedParameters.native_log_atTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T11:31:09.328718+00:00
-- url     : https://prove2.me/submissions/de61e077-eef6-48a1-bf46-82adfec99ba2

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySignedPadding
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySignedParameters
import Theorems.Thm_ThreeSum_Parameters_log_two_pos
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalOversizeRates_denominator_atTop
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalOversizeRates_native_rate_tendsto
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalParameters_Hpi_pos
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalParameters_log_two_pos
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalParameters_partitionEntropy_bounds


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
theorem _root_.solution {K : ℕ} (hK : 0<K) :
    Tendsto (fun m => Real.log (nativePrime K m : ℝ)) atTop atTop := by
  have hc : 0<(Hpi+partitionEntropy)/2+Hpi/K := by
    have hpart : 0<partitionEntropy := by linarith [partitionEntropy_bounds.1]
    exact add_pos (half_pos (add_pos Hpi_pos hpart))
      (div_pos Hpi_pos (by exact_mod_cast hK))
  have h := denominator_atTop.atTop_mul_pos hc (native_rate_tendsto hK)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
  unfold nativeRate
  have hlen : (fixedLength m : ℝ)≠0 := by
    have hp : 0<fixedLength m := by unfold fixedLength; positivity
    exact_mod_cast hp.ne'
  field_simp [hlen,log_two_pos.ne']
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalSignedParameters
