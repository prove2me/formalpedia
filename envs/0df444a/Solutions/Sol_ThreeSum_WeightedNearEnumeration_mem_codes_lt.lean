-- Prove2me | solution 1 for ThreeSum.WeightedNearEnumeration.mem_codes_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:06:09.082215+00:00
-- url     : https://prove2.me/submissions/98fe6b24-1b68-46a4-a82c-09cdb12e2cae

import Definitions.Def_Submission_Weighted_Addresses
import Definitions.Def_Submission_Weighted_NearEnumeration
import Theorems.Thm_ThreeSum_WeightedNearEnumeration_mem_digits
import Theorems.Thm_ThreeSum_WeightedNearEnumeration_mem_words
import Theorems.Thm_ThreeSum_WeightedNearEnumeration_admitted_length
import Theorems.Thm_ThreeSum_WeightedNearEnumeration_admitted_digits
import Theorems.Thm_ThreeSum_WeightedNearEnumeration_codes_eq_map
import Theorems.Thm_ThreeSum_WeightedNearEnumeration_codes_length
import Theorems.Thm_ThreeSum_TernaryAddresses_code_lt
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_eq_map
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_words
import Theorems.Thm_ThreeSum_WeightedAddresses_code_lt
import Theorems.Thm_ThreeSum_WeightedAddresses_codes_eq_map
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
attribute [local simp] ThreeSum.WeightedNearEnumeration.codes_length

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedNearEnumeration
open ThreeSum.WeightedAddresses ThreeSum.WeightedEnumeration
namespace ThreeSum.WeightedNearEnumeration
theorem _root_.solution {qs : List ℕ} {D a : ℕ}
    (hq : ∀ q ∈ qs, q < 3) (ha : a ∈ codes qs D) : a < 4^qs.length := by
  rw [codes_eq_map] at ha
  obtain ⟨rs,hrs,rfl⟩ := List.mem_map.mp ha
  have had := (mem_words qs rs D).mp hrs
  simpa only [admitted_length had] using code_lt rs (admitted_digits hq had)
end ThreeSum.WeightedNearEnumeration
