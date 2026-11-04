-- Prove2me | solution 1 for ThreeSum.LightTernaryPass.values_eq_coordinateZeta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:57:38.662134+00:00
-- url     : https://prove2.me/submissions/d28fba91-2cf3-4ca9-923d-8466a803c905

import Definitions.Def_Submission_ThreeSum_LightTernaryLookup
import Definitions.Def_Submission_ThreeSum_LightTernaryPass
import Theorems.Thm_Light_LocalsBut_update
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
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernaryQuery_zetaDigit_congr_below
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
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords



set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryPass
set_option maxHeartbeats 2000000
open Light ThreeSum.TernaryQuery ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightTernaryPass
theorem _root_.solution {N : ℕ} (enumeration : ℕ →
    ThreeSum.TernaryJointType.TritWord N) (i : Fin N)
    (digits : ℕ → Fin 3) (ix : Fin 3 → ℕ → ℕ)
    (F : ThreeSum.TernaryJointType.TritWord N → ℤ) (j : ℕ)
    (hdigit : digits j = enumeration j i)
    (hindex : ∀ e ≤ digits j, enumeration (ix e j) =
      Function.update (enumeration j) i e) :
    values digits ix (fun k => F (enumeration k)) j =
      coordinateZeta i F (enumeration j) := by
  unfold values coordinateZeta
  rw [← hdigit]
  apply zetaDigit_congr_below
  intro e he
  dsimp only
  rw [hindex e he]
end ThreeSum.LightTernaryPass
