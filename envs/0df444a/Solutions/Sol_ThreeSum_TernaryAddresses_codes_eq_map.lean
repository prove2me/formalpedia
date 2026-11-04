-- Prove2me | solution 1 for ThreeSum.TernaryAddresses.codes_eq_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:25:51.065217+00:00
-- url     : https://prove2.me/submissions/cb3be6d6-1e85-44e5-b83c-6fe5479f87a8

import Definitions.Def_Submission_ThreeSum_TernaryEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_words
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits



set_option autoImplicit false
open ThreeSum ThreeSum.TernaryAddresses
open ThreeSum.TernaryEnumeration
namespace ThreeSum.TernaryAddresses
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
    have hlen := ((mem_words n (t - d) xs).mp hx).1
    simp [code, hlen]
end ThreeSum.TernaryAddresses
