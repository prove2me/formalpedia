-- Prove2me | solution 1 for ThreeSum.TernaryNearEnumeration.codes_eq_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:01:47.131389+00:00
-- url     : https://prove2.me/submissions/c7d049c0-60da-4f16-ba7c-3cf690d22ab8

import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_mem_words
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_admitted_length
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_words
attribute [local simp] ThreeSum.TernaryAddresses.codes_length
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits


attribute [local simp] ThreeSum.TernaryNearEnumeration.mem_digits

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryNearEnumeration
open ThreeSum.TernaryAddresses
namespace ThreeSum.TernaryNearEnumeration
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
    have hl := admitted_length ((mem_words qs rs (D-(q-r))).mp hrs)
    simp [code,hl]
end ThreeSum.TernaryNearEnumeration
