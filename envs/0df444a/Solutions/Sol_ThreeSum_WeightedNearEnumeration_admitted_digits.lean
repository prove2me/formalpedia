-- Prove2me | solution 1 for ThreeSum.WeightedNearEnumeration.admitted_digits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:37:23.822209+00:00
-- url     : https://prove2.me/submissions/7a7af6d2-4cf4-4144-b03f-942a96e9d946

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
theorem _root_.solution {qs rs : List ℕ} {D : ℕ}
    (hq : ∀ q ∈ qs, q < 3) (h : Admitted qs rs D) : ∀ r ∈ rs, r < 3 := by
  induction qs generalizing rs D with
  | nil => cases rs <;> simp_all [Admitted]
  | cons q qs ih =>
    cases rs with
    | nil => simp [Admitted] at h
    | cons r rs =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact h.1.trans_lt (hq q (by simp))
      · exact ih (fun y hy => hq y (by simp [hy])) h.2.2 x hx
end ThreeSum.WeightedNearEnumeration
