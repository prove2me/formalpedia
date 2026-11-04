-- Prove2me | solution 1 for ThreeSum.TernaryCoverOutputCap.outputFiber_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:43:29.77999+00:00
-- url     : https://prove2.me/submissions/53d65f5d-553a-44ff-9fa0-4ad6fd554aee

import Definitions.Def_Submission_ThreeSum_TernaryCoverRegularity
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryCoverOutputCap
import Theorems.Thm_ThreeSum_TernaryCoverOutputCap_outputFiber_card_le_product
import Theorems.Thm_ThreeSum_TernaryCoverOutputCap_digit_product

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverOutputCap
open Finset TernaryJointType TernaryCoverLocal
variable {L : ℕ}
namespace ThreeSum.TernaryCoverOutputCap
theorem _root_.solution (α π : DigitType) (q : TritWord L) (hq : HasType q π) :
    Fintype.card (outputFiber α π q) ≤ 2^(π 1) * 3^(π 2) := by
  have h := outputFiber_card_le_product α π q
  rw [digit_product, hq 1, hq 2] at h
  exact h
end ThreeSum.TernaryCoverOutputCap
