-- Prove2me | solution 1 for ThreeSum.WeightedAddresses.codes_strictly_sorted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:30:24.750255+00:00
-- url     : https://prove2.me/submissions/df7337f9-b44d-4557-894f-f43e9b87bde5

import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_Weighted_Enumeration
import Definitions.Def_Submission_Weighted_Addresses
import Theorems.Thm_ThreeSum_WeightedAddresses_digitCode_strict
import Theorems.Thm_ThreeSum_WeightedAddresses_codes_length
import Theorems.Thm_ThreeSum_WeightedAddresses_mem_codes_lt
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryAddresses_digitCode_strict
import Theorems.Thm_ThreeSum_TernaryAddresses_mem_codes_lt
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


attribute [local simp] ThreeSum.WeightedAddresses.codes_length

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedAddresses
open ThreeSum.WeightedEnumeration
namespace ThreeSum.WeightedAddresses
theorem _root_.solution (n t : ℕ) : (codes n t).Pairwise (· < ·) := by
  induction n generalizing t with
  | zero => simp [codes]
  | succ n ih =>
    rw [codes, List.pairwise_flatMap]
    constructor
    · intro d hd
      rw [List.pairwise_map]
      exact (ih (t - digitCost d)).imp (fun h => Nat.add_lt_add_left h _)
    · have hdigits : (digits t).Pairwise (· < ·) :=
        List.pairwise_lt_range.filter _
      apply hdigits.imp_of_mem
      intro d e hd he hde a ha b hb
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
      have hd3 := (mem_digits.mp hd).1
      have he3 := (mem_digits.mp he).1
      have hdc := digitCode_strict hd3 he3 hde
      have hx4 := mem_codes_lt hx
      have hp : 0 < 4 ^ n := by positivity
      nlinarith
end ThreeSum.WeightedAddresses
