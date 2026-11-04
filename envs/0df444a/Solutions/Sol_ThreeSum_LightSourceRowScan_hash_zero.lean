-- Prove2me | solution 1 for ThreeSum.LightSourceRowScan.hash_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:40:24.361033+00:00
-- url     : https://prove2.me/submissions/25fde80f-ae4e-4d26-97cf-6b4e4460fbed

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightMaskBits
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_Submission_ThreeSum_LightSourceRowScan
import Theorems.Thm_ThreeSum_LightSourceRowScan_count_zero
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero


attribute [local simp] ThreeSum.LightSourceRowScan.count_zero

set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceRowScan
open Light Finset
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
namespace ThreeSum.LightSourceRowScan
theorem _root_.solution (bits w0 w1 : ℕ → ℕ) : hash bits w0 w1 0=0 := by simp [hash]
end ThreeSum.LightSourceRowScan
