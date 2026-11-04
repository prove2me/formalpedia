-- Prove2me | solution 1 for ThreeSum.WeightedEnumeration.words_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:28:28.11933+00:00
-- url     : https://prove2.me/submissions/edc3b195-92c6-4f58-82be-771853552636

import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Range
import Mathlib.Tactic
import Definitions.Def_Submission_Weighted_Enumeration
import Theorems.Thm_ThreeSum_WeightedEnumeration_zero_word_mem

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedEnumeration
namespace ThreeSum.WeightedEnumeration
theorem _root_.solution (n t : ℕ) : 0 < (words n t).length := by
  exact List.length_pos_of_mem (zero_word_mem n t)
end ThreeSum.WeightedEnumeration
