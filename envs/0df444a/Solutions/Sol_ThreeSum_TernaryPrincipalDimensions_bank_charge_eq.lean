-- Prove2me | solution 1 for ThreeSum.TernaryPrincipalDimensions.bank_charge_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:13:05.593489+00:00
-- url     : https://prove2.me/submissions/c67b5cb8-c6c6-46ab-97d1-c9675734f795

import Definitions.Def_Submission_ThreeSum_TernaryFiniteLedger
import Definitions.Def_Submission_ThreeSum_TernaryPrincipalDimensions
import Theorems.Thm_ThreeSum_TernaryPrincipalDimensions_output_log_pos
import Theorems.Thm_ThreeSum_TernaryEntropyRates_denominator_pos


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPrincipalDimensions
open Real TernaryParameters TernaryEntropyRates TernaryDimensionBounds
open TernaryCoverScale TernaryLocalParameters TernaryFiniteLedger
namespace ThreeSum.TernaryPrincipalDimensions
theorem _root_.solution {m : ℕ} (hm : 0 < m) :
    2*((fixedLength m : ℝ)*Real.log 2*bankEntropy)/Real.log (outputSize m : ℝ)=bankCharge m := by
  unfold bankCharge outputRate
  field_simp [output_log_pos hm |>.ne',denominator_pos hm |>.ne']
end ThreeSum.TernaryPrincipalDimensions
