-- Prove2me | solution 1 for ThreeSum.TernaryPrincipalDimensions.endpoint_charge_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:12:28.966389+00:00
-- url     : https://prove2.me/submissions/82846acd-45a1-42d7-8635-1df146672e82

import Definitions.Def_Submission_ThreeSum_TernaryFiniteLedger
import Definitions.Def_Submission_ThreeSum_TernaryPrincipalDimensions
import Theorems.Thm_ThreeSum_TernaryPrincipalDimensions_output_log_pos
import Theorems.Thm_ThreeSum_Parameters_log_two_pos
import Theorems.Thm_ThreeSum_TernaryParameters_log_two_pos


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPrincipalDimensions
open Real TernaryParameters TernaryEntropyRates TernaryDimensionBounds
open TernaryCoverScale TernaryLocalParameters TernaryFiniteLedger
namespace ThreeSum.TernaryPrincipalDimensions
theorem _root_.solution {m : ℕ} (hm : 0 < m) :
    2*Real.log (endpointSize m : ℝ)/Real.log (outputSize m : ℝ)=endpointCharge m := by
  unfold endpointCharge endpointRate outputRate
  have hL : (fixedLength m : ℝ) ≠ 0 := by unfold fixedLength; exact_mod_cast (Nat.mul_pos (by decide : 0 < 100000000) hm).ne'
  field_simp [output_log_pos hm |>.ne',hL,log_two_pos.ne'] <;> ring
end ThreeSum.TernaryPrincipalDimensions
