-- Prove2me | solution 1 for ThreeSum.LightTernaryCarryCodes.row_carry_read
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:20:34.946509+00:00
-- url     : https://prove2.me/submissions/d6a9ea3a-b5c9-4237-a6ef-0556a5ae7a87

import Definitions.Def_Submission_ThreeSum_LightOutputDecodeDigits
import Definitions.Def_Submission_ThreeSum_TernaryCarryCode
import Definitions.Def_Submission_ThreeSum_LightNatPower
import Definitions.Def_Submission_ThreeSum_LightTernaryCarryCodes
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_TernarySignedDigits_carryNat_zero
import Theorems.Thm_ThreeSum_TernarySignedReduction_mem_carryCatalog
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.TernarySignedDigits.carryNat_zero
attribute [local simp] ThreeSum.TernarySignedReduction.mem_carryCatalog



set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryCarryCodes
open Light TernarySignedDigits
set_option maxHeartbeats 2400000
set_option maxRecDepth 9000
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
namespace ThreeSum.LightTernaryCarryCodes
theorem _root_.solution {ν : ℕ → ℤ} {dst J q : ℕ}
    (h : Row ν dst J q) (i : Fin (J+1)) :
    ν (dst+J-i.val)=((TernaryCarryCode.carryFromCode J q i).val : ℤ) := by
  by_cases hi : i.val<J
  · simpa only [TernaryCarryCode.carryFromCode,dif_pos hi] using h.2 i.val hi
  · have he : i.val=J := by omega
    simp only [TernaryCarryCode.carryFromCode,dif_neg hi]
    simpa only [he,Nat.add_sub_cancel,Fin.val_zero,Int.natCast_zero] using h.1
end ThreeSum.LightTernaryCarryCodes
