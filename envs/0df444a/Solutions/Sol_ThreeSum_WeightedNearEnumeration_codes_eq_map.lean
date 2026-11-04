-- Prove2me | solution 1 for ThreeSum.WeightedNearEnumeration.codes_eq_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:01:35.995667+00:00
-- url     : https://prove2.me/submissions/5c83fd61-5532-46bb-aff5-0c186b8e026f

import Definitions.Def_Submission_Weighted_Addresses
import Definitions.Def_Submission_Weighted_NearEnumeration
import Theorems.Thm_ThreeSum_WeightedNearEnumeration_mem_digits
import Theorems.Thm_ThreeSum_WeightedNearEnumeration_mem_words
import Theorems.Thm_ThreeSum_WeightedNearEnumeration_admitted_length
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_words
import Theorems.Thm_ThreeSum_WeightedAddresses_codes_length
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_one
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_two
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_zero
import Theorems.Thm_ThreeSum_WeightedEnumeration_mem_digits
import Theorems.Thm_ThreeSum_WeightedEnumeration_mem_words
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
theorem _root_.solution (qs : List ℕ) (D : ℕ) : codes qs D = (words qs D).map code := by
  induction qs generalizing D with
  | nil => simp [codes,words,code]
  | cons q qs ih =>
    simp only [codes,words,List.map_flatMap]
    congr 1
    funext r
    rw [ih]
    simp only [List.map_map]
    apply List.map_congr_left
    intro rs hrs
    have hl := admitted_length ((mem_words qs rs (D-(digitCost q-digitCost r))).mp hrs)
    simp [code,hl]
end ThreeSum.WeightedNearEnumeration
