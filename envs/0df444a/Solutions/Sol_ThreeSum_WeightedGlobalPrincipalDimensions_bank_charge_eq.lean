-- Prove2me | solution 1 for ThreeSum.WeightedGlobalPrincipalDimensions.bank_charge_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:03:08.101269+00:00
-- url     : https://prove2.me/submissions/ff718c8a-3890-4959-b15d-7640a03142d2

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryFiniteLedger
import Definitions.Def_Submission_Weighted_Global_TernaryPrincipalDimensions
import Theorems.Thm_ThreeSum_WeightedGlobalPrincipalDimensions_output_log_pos
import Theorems.Thm_ThreeSum_WeightedGlobalEntropyRates_denominator_pos


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalPrincipalDimensions
open Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalDimensionBounds
open WeightedGlobalCoverScale WeightedGlobalLocalParameters WeightedGlobalFiniteLedger
namespace ThreeSum.WeightedGlobalPrincipalDimensions
theorem _root_.solution {m : ℕ} (hm : 0 < m) :
    2*((fixedLength m : ℝ)*Real.log 2*bankEntropy)/Real.log (outputSize m : ℝ)=bankCharge m := by
  unfold bankCharge outputRate
  field_simp [output_log_pos hm |>.ne',denominator_pos hm |>.ne']
end ThreeSum.WeightedGlobalPrincipalDimensions
