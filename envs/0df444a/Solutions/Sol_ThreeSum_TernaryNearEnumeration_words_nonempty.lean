-- Prove2me | solution 1 for ThreeSum.TernaryNearEnumeration.words_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:01:44.630721+00:00
-- url     : https://prove2.me/submissions/b0c7ef4a-5d99-4f90-afe4-d9e4076c0adf

import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_mem_words
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_self_admitted
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_words


set_option autoImplicit false
open ThreeSum ThreeSum.TernaryNearEnumeration
open ThreeSum.TernaryAddresses
namespace ThreeSum.TernaryNearEnumeration
theorem _root_.solution (qs : List ℕ) (D : ℕ) : 0 < (words qs D).length :=
  List.length_pos_of_mem ((mem_words qs qs D).mpr (self_admitted qs D))
end ThreeSum.TernaryNearEnumeration
