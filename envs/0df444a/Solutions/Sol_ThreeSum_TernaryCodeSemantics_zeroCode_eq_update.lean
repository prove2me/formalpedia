-- Prove2me | solution 1 for ThreeSum.TernaryCodeSemantics.zeroCode_eq_update
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:38:28.988794+00:00
-- url     : https://prove2.me/submissions/b993813e-3cb2-43c8-b69e-50bb499132a1

import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Theorems.Thm_ThreeSum_TernaryCodeSemantics_support_subset
import Theorems.Thm_ThreeSum_TernaryCodeSemantics_address_eq_maskOf
import Theorems.Thm_ThreeSum_TernaryCodeSemantics_support_update_zero
import Theorems.Thm_Light_LocalsBut_update
import Definitions.Def_WeightedCache3SUM_Alias_c15dd3b5e05b2f5c
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_high
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low


set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCodeSemantics
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryAddresses
open ThreeSum.TernaryBankEnumeration ThreeSum.SubsetAddress ThreeSum.MaskErase
set_option maxHeartbeats 2000000
namespace ThreeSum.TernaryCodeSemantics
theorem _root_.solution {N : ℕ} (w : TritWord N) (i : Fin N) :
    LightTernaryCodes.zeroCode (2*N) (low i) (high i) (address w) =
      address (Function.update w i 0) := by
  unfold LightTernaryCodes.zeroCode
  rw [address_eq_maskOf,eraseMask_maskOf _ (support_subset w)]
  rw [eraseMask_maskOf _ ((Finset.erase_subset _ _).trans (support_subset w))]
  rw [address_eq_maskOf,support_update_zero]
end ThreeSum.TernaryCodeSemantics
