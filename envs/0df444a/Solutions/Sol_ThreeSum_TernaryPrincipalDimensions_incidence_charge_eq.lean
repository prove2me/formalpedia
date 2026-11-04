-- Prove2me | solution 1 for ThreeSum.TernaryPrincipalDimensions.incidence_charge_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:13:48.595963+00:00
-- url     : https://prove2.me/submissions/061f0132-3e6c-4918-af58-7f2712856b8d

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
    1+2*incidenceSlope m/Real.log (outputSize m : ℝ)=incidenceCharge m := by
  unfold incidenceCharge incidenceSlope outputRate primeRate
  have hL : (fixedLength m : ℝ) ≠ 0 := by unfold fixedLength; exact_mod_cast (Nat.mul_pos (by decide : 0 < 100000000) hm).ne'
  field_simp [output_log_pos hm |>.ne',hL,log_two_pos.ne'] <;> ring
end ThreeSum.TernaryPrincipalDimensions
