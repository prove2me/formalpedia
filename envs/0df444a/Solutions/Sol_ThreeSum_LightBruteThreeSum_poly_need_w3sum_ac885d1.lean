-- Prove2me | solution 1 for ThreeSum.LightBruteThreeSum.poly_need_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:07:18.916343+00:00
-- url     : https://prove2.me/submissions/7a5d8c3c-f7cc-45c8-9703-f631dab64c38

import Definitions.Def_Submission_ThreeSum_LightOriginalTripleScan
import Definitions.Def_Submission_ThreeSum_OriginalThreeSum
import Definitions.Def_Submission_ThreeSum_LightBruteThreeSum
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSumApsp_Spec_length_affL
import Theorems.Thm_ThreeSumApsp_Spec_length_subMat
import Theorems.Thm_ThreeSum_ColorClassLists_value_fin
import Theorems.Thm_ThreeSum_LightClassFilter_items_zero
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
attribute [local simp] ThreeSum.ColorClassLists.value_fin
attribute [local simp] ThreeSum.LightClassFilter.items_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSumApsp.Spec.length_affL
attribute [local simp] ThreeSumApsp.Spec.length_subMat



set_option autoImplicit false
open ThreeSum ThreeSum.LightBruteThreeSum
open Light ThreeSumApsp.Spec
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightBruteThreeSum
theorem _root_.solution : PolyNeed need := by
  refine ⟨5,3,fun n U => ?_⟩
  let B : ℕ := ((n+1)*(U+1))^3
  have hbaseN : n+1 ≤ (n+1)*(U+1) := Nat.le_mul_of_pos_right _ (by omega)
  have hbaseU : U+1 ≤ (n+1)*(U+1) := Nat.le_mul_of_pos_left _ (by omega)
  have hbase : 1 ≤ (n+1)*(U+1) := Nat.mul_le_mul (by omega : 1 ≤ n+1) (by omega : 1 ≤ U+1)
  have hcube : (n+1)*(U+1) ≤ B := by
    have hh := Nat.le_mul_of_pos_left ((n+1)*(U+1))
      (Nat.one_le_pow 2 _ hbase)
    simpa only [B,pow_succ,pow_zero,one_mul] using hh
  have hN : n ≤ B := (by omega : n ≤ n+1).trans (hbaseN.trans hcube)
  have hU : U ≤ B := (by omega : U ≤ U+1).trans (hbaseU.trans hcube)
  have hN3 : n^3 ≤ B := Nat.pow_le_pow_left (by omega : n ≤ (n+1)*(U+1)) 3
  have h1 : 1 ≤ B := Nat.one_le_pow _ _ hbase
  have hp : polyBound 5 3 [n,U]=32*B := by simp [polyBound,B]
  rw [hp]
  simp only [need,LightOriginalTripleRow.word]
  omega
end ThreeSum.LightBruteThreeSum
