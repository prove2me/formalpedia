-- Prove2me | solution 1 for ThreeSum.WeightedGlobalPrincipalDimensions.histogram_charge_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:03:09.45646+00:00
-- url     : https://prove2.me/submissions/0c0ee903-59e8-41a1-8e6f-37f7950309dd

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryFiniteLedger
import Definitions.Def_Submission_Weighted_Global_TernaryPrincipalDimensions
import Theorems.Thm_ThreeSum_WeightedGlobalPrincipalDimensions_output_log_pos
import Theorems.Thm_ThreeSum_Parameters_log_two_pos
import Theorems.Thm_ThreeSum_WeightedGlobalParameters_log_two_pos


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalPrincipalDimensions
open Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalDimensionBounds
open WeightedGlobalCoverScale WeightedGlobalLocalParameters WeightedGlobalFiniteLedger
namespace ThreeSum.WeightedGlobalPrincipalDimensions
theorem _root_.solution {m : ℕ} (hm : 0 < m) :
    2*Real.log (prime m : ℝ)/Real.log (outputSize m : ℝ)=histogramCharge m := by
  unfold histogramCharge primeRate outputRate
  have hL : (fixedLength m : ℝ) ≠ 0 := by unfold fixedLength; exact_mod_cast (Nat.mul_pos (by decide : 0 < 30000000000000) hm).ne'
  field_simp [output_log_pos hm |>.ne',hL,log_two_pos.ne'] <;> ring
end ThreeSum.WeightedGlobalPrincipalDimensions
