-- Prove2me | solution 1 for ThreeSum.LightSourceRowScan.hash_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:08:06.785893+00:00
-- url     : https://prove2.me/submissions/89c44ea1-4d2d-44b8-a142-ff025081b81d

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightMaskBits
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_Submission_ThreeSum_LightSourceRowScan
import Theorems.Thm_ThreeSum_LightSourceRowScan_count_zero
import Theorems.Thm_ThreeSum_LightSourceRowScan_hash_zero
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
attribute [local simp] ThreeSum.LightSourceRowScan.hash_zero

set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceRowScan
open Light Finset
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
namespace ThreeSum.LightSourceRowScan
theorem _root_.solution {L j U : ℕ} (bits w0 w1 : ℕ → ℕ)
    (h0 : ∀ i < L, w0 i ≤ U) (h1 : ∀ i < L, w1 i ≤ U) (hj : j ≤ L) :
    hash bits w0 w1 j ≤ j*U := by
  unfold hash
  calc
    _ ≤ ∑ _i ∈ range j, U := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' := (mem_range.mp hi).trans_le hj
      split
      · exact h1 i hi'
      · exact h0 i hi'
    _ = j*U := by simp
end ThreeSum.LightSourceRowScan
