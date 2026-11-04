-- Prove2me | solution 1 for ThreeSum.LightTernaryInversePass.values_eq_coordinateInverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:58:58.802661+00:00
-- url     : https://prove2.me/submissions/8e1f2f30-5b01-4355-acb4-cea7cb975c8a

import Definitions.Def_Submission_ThreeSum_LightTernaryLookup
import Definitions.Def_Submission_ThreeSum_LightTernaryInversePass
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
import Theorems.Thm_ThreeSum_TernaryQuery_inverseDigit_congr_below
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
open ThreeSum ThreeSum.LightTernaryInversePass
set_option maxHeartbeats 2000000
open Light ThreeSum.TernaryQuery ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightTernaryInversePass
theorem _root_.solution {N : ℕ} (enumeration : ℕ →
    ThreeSum.TernaryJointType.TritWord N) (i : Fin N)
    (digits : ℕ → Fin 3) (ix : Fin 3 → ℕ → ℕ)
    (F : ThreeSum.TernaryJointType.TritWord N → ℤ) (j : ℕ)
    (hdigit : digits j = enumeration j i)
    (hindex : ∀ e ≤ digits j, enumeration (ix e j) =
      Function.update (enumeration j) i e) :
    values digits ix (fun k => F (enumeration k)) j =
      coordinateInverse i F (enumeration j) := by
  unfold values coordinateInverse
  rw [← hdigit]
  apply inverseDigit_congr_below
  intro e he
  dsimp only
  rw [hindex e he]
end ThreeSum.LightTernaryInversePass
