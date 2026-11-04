-- Prove2me | solution 1 for ThreeSum.WeightedGlobalPairedCollisionRate.charge_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:41:28.97646+00:00
-- url     : https://prove2.me/submissions/c1447447-4559-4016-a392-f513c24075a9

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryPairedFamilyMargin
import Definitions.Def_Submission_ThreeSum_TernaryPairedRecurrence
import Definitions.Def_Submission_Weighted_Global_TernaryPairedCollisionRate
import Theorems.Thm_ThreeSum_Parameters_log_two_pos
import Theorems.Thm_ThreeSum_WeightedGlobalParameters_log_two_pos
import Theorems.Thm_ThreeSum_WeightedGlobalPrincipalDimensions_output_log_pos


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalPairedCollisionRate
open Filter Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalOversizeRates WeightedGlobalOversizePrime
open WeightedGlobalCoverScale WeightedGlobalLocalParameters
open scoped Topology
set_option maxHeartbeats 1000000
namespace ThreeSum.WeightedGlobalPairedCollisionRate
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
end ThreeSum.WeightedGlobalPairedCollisionRate
