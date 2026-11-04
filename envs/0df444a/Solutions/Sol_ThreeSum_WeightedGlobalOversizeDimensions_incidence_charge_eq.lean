-- Prove2me | solution 1 for ThreeSum.WeightedGlobalOversizeDimensions.incidence_charge_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:14:53.862715+00:00
-- url     : https://prove2.me/submissions/f1877a33-55ea-4380-9c97-0c07f8c12e37

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeOverhead
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeDimensions
import Theorems.Thm_ThreeSum_Parameters_log_two_pos
import Theorems.Thm_ThreeSum_WeightedGlobalEntropyRates_partition_log
import Theorems.Thm_ThreeSum_WeightedGlobalParameters_log_two_pos
import Theorems.Thm_ThreeSum_WeightedGlobalPrincipalDimensions_output_log_pos


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalOversizeDimensions
open Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open WeightedGlobalLocalParameters WeightedGlobalOversizePrime WeightedGlobalOversizeRates
open WeightedGlobalPrincipalDimensions WeightedGlobalDimensionBounds TernaryJointType
namespace ThreeSum.WeightedGlobalOversizeDimensions
theorem _root_.solution {K m : ℕ} (hm : 0 < m) :
    1+2*incidenceSlope K m/Real.log (outputSize m : ℝ)=WeightedGlobalOversizeRates.incidenceCharge K m := by
  unfold WeightedGlobalOversizeRates.incidenceCharge incidenceSlope familyCharge outputRate nativeRate inflationRate
  rw [partition_log]
  have hLen : (fixedLength m : ℝ) ≠ 0 := by
    have hh : 0 < fixedLength m := by unfold fixedLength; positivity
    exact_mod_cast hh.ne'
  field_simp [output_log_pos hm |>.ne',hLen,log_two_pos.ne'] <;> ring
end ThreeSum.WeightedGlobalOversizeDimensions
