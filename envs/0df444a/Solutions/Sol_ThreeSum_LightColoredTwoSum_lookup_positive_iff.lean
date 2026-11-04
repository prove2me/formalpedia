-- Prove2me | solution 1 for ThreeSum.LightColoredTwoSum.lookup_positive_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:20:27.914821+00:00
-- url     : https://prove2.me/submissions/45cba53a-05f9-4e20-991e-22e977ec58d7

import Definitions.Def_Submission_ThreeSum_LightBandLookup
import Definitions.Def_Submission_ThreeSum_LightColoredTwoSum
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Definitions.Def_WeightedCache3SUM_Alias_b4f931c7e067a8b6
import Definitions.Def_WeightedCache3SUM_Alias_f0b9790e2f96cf93
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



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightColoredTwoSum
open Light ThreeSum.LightSubsetAddress
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000
set_option maxRecDepth 12000
namespace ThreeSum.LightColoredTwoSum
theorem _root_.solution (target : ℕ → ℤ) (m : ℕ) (x : ℤ)
    (hs : ∀ i j, i<j → j<m → target i<target j) :
    0<LightBandLookup.result target target m x ↔ ∃ j<m, target j=x := by
  have hle : ∀ i j, i≤j → j<m → target i≤target j := by
    intro i j hij hj
    rcases eq_or_lt_of_le hij with rfl | hlt
    · rfl
    · exact (hs i j hlt hj).le
  constructor
  · intro hp
    cases he : BinarySearch.locate target target m x with
    | none => simp [LightBandLookup.result,he] at hp
    | some j =>
      have hh := BinarySearch.locate_sound target target m x hle he
      exact ⟨j,hh.1,le_antisymm hh.2.1 hh.2.2⟩
  · rintro ⟨j,hj,he⟩
    have hh := BinarySearch.locate_complete target target m x hle hs hj (by omega) (by omega)
    simp [LightBandLookup.result,hh]
end ThreeSum.LightColoredTwoSum
