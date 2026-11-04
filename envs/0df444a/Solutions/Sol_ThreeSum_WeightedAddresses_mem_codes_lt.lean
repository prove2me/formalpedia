-- Prove2me | solution 1 for ThreeSum.WeightedAddresses.mem_codes_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:29:16.309203+00:00
-- url     : https://prove2.me/submissions/d70f1ba1-ee8b-4417-96b3-503aa03acbd5

import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_Weighted_Enumeration
import Definitions.Def_Submission_Weighted_Addresses
import Theorems.Thm_ThreeSum_WeightedAddresses_code_lt
import Theorems.Thm_ThreeSum_WeightedAddresses_codes_eq_map
import Theorems.Thm_ThreeSum_WeightedAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryAddresses_code_lt
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_eq_map
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


attribute [local simp] ThreeSum.WeightedAddresses.codes_length

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedAddresses
open ThreeSum.WeightedEnumeration
namespace ThreeSum.WeightedAddresses
theorem _root_.solution {n t a : ℕ} (ha : a ∈ codes n t) : a < 4 ^ n := by
  rw [codes_eq_map] at ha
  obtain ⟨xs, hx, rfl⟩ := List.mem_map.mp ha
  obtain ⟨hlen, hall, _⟩ := (mem_words n t xs).mp hx
  simpa [hlen] using code_lt xs hall
end ThreeSum.WeightedAddresses
