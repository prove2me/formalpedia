-- Prove2me | solution 1 for ThreeSum.WeightedAddresses.codes_eq_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:27:43.113724+00:00
-- url     : https://prove2.me/submissions/4159e6ef-248d-44f8-82da-94052d513635

import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_Weighted_Enumeration
import Definitions.Def_Submission_Weighted_Addresses
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_words
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_one
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_two
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_zero
import Theorems.Thm_ThreeSum_WeightedEnumeration_mem_digits
import Theorems.Thm_ThreeSum_WeightedEnumeration_mem_words
attribute [local simp] ThreeSum.TernaryAddresses.codes_length
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_one
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_two
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_zero
attribute [local simp] ThreeSum.WeightedEnumeration.mem_digits



set_option autoImplicit false
open ThreeSum ThreeSum.WeightedAddresses
open ThreeSum.WeightedEnumeration
namespace ThreeSum.WeightedAddresses
theorem _root_.solution (n t : ℕ) : codes n t = (words n t).map code := by
  induction n generalizing t with
  | zero => simp [codes, words, code]
  | succ n ih =>
    simp only [codes, words, List.map_flatMap]
    congr 1
    funext d
    rw [ih]
    simp only [List.map_map]
    apply List.map_congr_left
    intro xs hx
    have hlen := ((mem_words n (t - digitCost d) xs).mp hx).1
    simp [code, hlen]
end ThreeSum.WeightedAddresses
