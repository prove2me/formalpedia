-- Prove2me | solution 1 for ThreeSum.TernaryCodeSemantics.oneCode_eq_update
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:39:40.729423+00:00
-- url     : https://prove2.me/submissions/045d1859-3082-4ddc-a8eb-803feafef958

import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Theorems.Thm_ThreeSum_TernaryCodeSemantics_support_subset
import Theorems.Thm_ThreeSum_TernaryCodeSemantics_address_eq_maskOf
import Theorems.Thm_ThreeSum_TernaryCodeSemantics_support_update_one
import Theorems.Thm_Light_LocalsBut_update
import Definitions.Def_WeightedCache3SUM_Alias_c15dd3b5e05b2f5c
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_high


set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCodeSemantics
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryAddresses
open ThreeSum.TernaryBankEnumeration ThreeSum.SubsetAddress ThreeSum.MaskErase
set_option maxHeartbeats 2000000
namespace ThreeSum.TernaryCodeSemantics
theorem _root_.solution {N : ℕ} (w : TritWord N) (i : Fin N) :
    LightTernaryCodes.oneCode (2*N) (high i) (address w) =
      address (Function.update w i (clampOne (w i))) := by
  unfold LightTernaryCodes.oneCode
  rw [address_eq_maskOf,eraseMask_maskOf _ (support_subset w),
    address_eq_maskOf,support_update_one]
end ThreeSum.TernaryCodeSemantics
