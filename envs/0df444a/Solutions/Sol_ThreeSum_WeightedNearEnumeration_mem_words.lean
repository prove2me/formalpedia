-- Prove2me | solution 1 for ThreeSum.WeightedNearEnumeration.mem_words
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:37:19.215202+00:00
-- url     : https://prove2.me/submissions/d78c71ac-f216-4875-a36a-3f1d7066434d

import Definitions.Def_Submission_Weighted_Addresses
import Definitions.Def_Submission_Weighted_NearEnumeration
import Theorems.Thm_ThreeSum_WeightedNearEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_WeightedAddresses_codes_length
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_one
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_two
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_zero
import Theorems.Thm_ThreeSum_WeightedEnumeration_mem_digits
attribute [local simp] ThreeSum.TernaryAddresses.codes_length
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits
attribute [local simp] ThreeSum.WeightedAddresses.codes_length
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_one
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_two
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_zero
attribute [local simp] ThreeSum.WeightedEnumeration.mem_digits


attribute [local simp] ThreeSum.WeightedNearEnumeration.mem_digits

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedNearEnumeration
open ThreeSum.WeightedAddresses ThreeSum.WeightedEnumeration
namespace ThreeSum.WeightedNearEnumeration
theorem _root_.solution (qs rs : List ℕ) (D : ℕ) : rs ∈ words qs D ↔ Admitted qs rs D := by
  induction qs generalizing rs D with
  | nil => cases rs <;> simp [words,Admitted]
  | cons q qs ih =>
    cases rs with
    | nil => simp [words,Admitted]
    | cons r rs =>
      simp only [words,List.mem_flatMap,List.mem_map]
      constructor
      · rintro ⟨d,hd,xs,hxs,he⟩
        obtain ⟨rfl,rfl⟩ := List.cons.inj he
        exact ⟨(mem_digits.mp hd).1,(mem_digits.mp hd).2,(ih _ _).mp hxs⟩
      · rintro ⟨hr,hD,hrest⟩
        exact ⟨r,mem_digits.mpr ⟨hr,hD⟩,rs,(ih _ _).mpr hrest,rfl⟩
end ThreeSum.WeightedNearEnumeration
