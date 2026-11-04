-- Prove2me | solution 1 for ThreeSum.TernaryAddresses.codes_strictly_sorted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:28:12.818186+00:00
-- url     : https://prove2.me/submissions/14b8dce9-6c16-4977-958b-9f75f69b6408

import Definitions.Def_Submission_ThreeSum_TernaryEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Theorems.Thm_ThreeSum_TernaryAddresses_digitCode_strict
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryAddresses_mem_codes_lt
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits


attribute [local simp] ThreeSum.TernaryAddresses.codes_length

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryAddresses
open ThreeSum.TernaryEnumeration
namespace ThreeSum.TernaryAddresses
theorem _root_.solution (n t : ℕ) : (codes n t).Pairwise (· < ·) := by
  induction n generalizing t with
  | zero => simp [codes]
  | succ n ih =>
    rw [codes, List.pairwise_flatMap]
    constructor
    · intro d hd
      rw [List.pairwise_map]
      exact (ih (t - d)).imp (fun h => Nat.add_lt_add_left h _)
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
end ThreeSum.TernaryAddresses
