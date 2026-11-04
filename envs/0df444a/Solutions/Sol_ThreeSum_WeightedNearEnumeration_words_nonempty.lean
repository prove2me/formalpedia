-- Prove2me | solution 1 for ThreeSum.WeightedNearEnumeration.words_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:01:33.612497+00:00
-- url     : https://prove2.me/submissions/46ed1e0c-0cbc-4549-8508-ac5ece133033

import Definitions.Def_Submission_Weighted_Addresses
import Definitions.Def_Submission_Weighted_NearEnumeration
import Theorems.Thm_ThreeSum_WeightedNearEnumeration_mem_words
import Theorems.Thm_ThreeSum_WeightedNearEnumeration_self_admitted
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_words
import Theorems.Thm_ThreeSum_WeightedEnumeration_mem_words


set_option autoImplicit false
open ThreeSum ThreeSum.WeightedNearEnumeration
open ThreeSum.WeightedAddresses ThreeSum.WeightedEnumeration
namespace ThreeSum.WeightedNearEnumeration
theorem _root_.solution (qs : List ℕ) (D : ℕ) : 0 < (words qs D).length :=
  List.length_pos_of_mem ((mem_words qs qs D).mpr (self_admitted qs D))
end ThreeSum.WeightedNearEnumeration
