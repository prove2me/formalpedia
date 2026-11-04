-- Prove2me | solution 1 for ThreeSum.TernaryNearEnumeration.mem_words
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:37:42.291203+00:00
-- url     : https://prove2.me/submissions/6fd63582-a274-4818-9535-f6566992c60e

import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
attribute [local simp] ThreeSum.TernaryAddresses.codes_length
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits


attribute [local simp] ThreeSum.TernaryNearEnumeration.mem_digits

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryNearEnumeration
open ThreeSum.TernaryAddresses
namespace ThreeSum.TernaryNearEnumeration
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
end ThreeSum.TernaryNearEnumeration
