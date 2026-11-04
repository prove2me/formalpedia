-- Prove2me | solution 1 for ThreeSum.TernaryNearEnumeration.codes_strictly_sorted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:08:26.431714+00:00
-- url     : https://prove2.me/submissions/17b9599f-95b3-45d8-8066-98f0bda05e03

import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_codes_length
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_mem_codes_lt
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryAddresses_digitCode_strict
import Theorems.Thm_ThreeSum_TernaryAddresses_mem_codes_lt
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
attribute [local simp] ThreeSum.TernaryAddresses.codes_length
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits


attribute [local simp] ThreeSum.TernaryNearEnumeration.mem_digits
attribute [local simp] ThreeSum.TernaryNearEnumeration.codes_length

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryNearEnumeration
open ThreeSum.TernaryAddresses
namespace ThreeSum.TernaryNearEnumeration
theorem _root_.solution (qs : List ℕ) (D : ℕ) (hq : ∀ q ∈ qs, q < 3) :
    (codes qs D).Pairwise (· < ·) := by
  induction qs generalizing D with
  | nil => simp [codes]
  | cons q qs ih =>
    have hq0 := hq q (by simp)
    have htail : ∀ q ∈ qs, q < 3 := fun r hr => hq r (by simp [hr])
    rw [codes,List.pairwise_flatMap]
    constructor
    · intro r hr
      rw [List.pairwise_map]
      exact (ih _ htail).imp (fun h => Nat.add_lt_add_left h _)
    · have hdigits : (digits q D).Pairwise (· < ·) := List.pairwise_lt_range.filter _
      apply hdigits.imp_of_mem
      intro r s hr hs hrs a ha b hb
      obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ha
      obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hb
      have hr3 := ((mem_digits.mp hr).1).trans_lt hq0
      have hs3 := ((mem_digits.mp hs).1).trans_lt hq0
      have hdc := digitCode_strict hr3 hs3 hrs
      have hx4 := mem_codes_lt htail hx
      have hp : 0 < 4^qs.length := by positivity
      nlinarith
end ThreeSum.TernaryNearEnumeration
