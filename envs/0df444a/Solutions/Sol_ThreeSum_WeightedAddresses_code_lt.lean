-- Prove2me | solution 1 for ThreeSum.WeightedAddresses.code_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:27:26.935272+00:00
-- url     : https://prove2.me/submissions/ed149686-5b04-4283-9104-8df497e7eb5d

import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_Weighted_Enumeration
import Definitions.Def_Submission_Weighted_Addresses
import Theorems.Thm_ThreeSum_WeightedAddresses_digitCode_le
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryAddresses_digitCode_le
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_one
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_two
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_zero
import Theorems.Thm_ThreeSum_WeightedEnumeration_mem_digits
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
theorem _root_.solution (xs : List ℕ) (h : ∀ d ∈ xs, d < 3) : code xs < 4 ^ xs.length := by
  induction xs with
  | nil => simp [code]
  | cons d xs ih =>
    have hd := digitCode_le (h d (by simp))
    have hx := ih (fun e he => h e (by simp [he]))
    have hp : 0 < 4 ^ xs.length := by positivity
    simp only [code, List.length_cons, pow_succ]
    nlinarith
end ThreeSum.WeightedAddresses
