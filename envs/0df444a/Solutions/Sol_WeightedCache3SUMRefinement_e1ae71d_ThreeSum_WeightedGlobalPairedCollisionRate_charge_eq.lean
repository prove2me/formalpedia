-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPairedCollisionRate.charge_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T11:30:44.2762+00:00
-- url     : https://prove2.me/submissions/c9505bf9-711c-49e2-a9b5-0a3e3b477975

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPairedFamilyMargin
import Definitions.Def_Submission_ThreeSum_TernaryPairedRecurrence
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPairedCollisionRate
import Theorems.Thm_ThreeSum_Parameters_log_two_pos
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalParameters_log_two_pos
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalPrincipalDimensions_output_log_pos


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
theorem _root_.solution {K m : ℕ} (hm : 0<m) :
    charge K m=2+2*Real.log (9/(nativePrime K m : ℝ))/Real.log (outputSize m : ℝ) := by
  have hp : (0 : ℝ)<nativePrime K m := by exact_mod_cast (nativePrime_prime K m).pos
  have hLen : (fixedLength m : ℝ)≠0 := by
    have hh : 0<fixedLength m := by unfold fixedLength; omega
    exact_mod_cast hh.ne'
  unfold charge nativeRate outputRate
  rw [Real.log_div (by norm_num) hp.ne']
  field_simp [hLen,log_two_pos.ne',WeightedGlobalPrincipalDimensions.output_log_pos hm |>.ne']
  ring
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPairedCollisionRate
