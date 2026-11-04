-- Prove2me | solution 1 for ThreeSum.TernaryCodeSemantics.digit_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:34:30.779578+00:00
-- url     : https://prove2.me/submissions/bf1bffd4-831b-48dd-857d-fe6205632738

import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Theorems.Thm_ThreeSum_TernaryCodeSemantics_low_bit
import Theorems.Thm_ThreeSum_TernaryCodeSemantics_high_bit
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_high
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low


set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCodeSemantics
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryAddresses
open ThreeSum.TernaryBankEnumeration ThreeSum.SubsetAddress ThreeSum.MaskErase
set_option maxHeartbeats 2000000
namespace ThreeSum.TernaryCodeSemantics
theorem _root_.solution {N : ℕ} (w : TritWord N) (i : Fin N) :
    LightTernaryCodes.digit (2*N) (low i) (high i) (address w)=(w i).val := by
  unfold LightTernaryCodes.digit
  rw [low_bit,high_bit]
  generalize hd : w i=d
  fin_cases d <;> norm_num [Fin.ext_iff]
end ThreeSum.TernaryCodeSemantics
