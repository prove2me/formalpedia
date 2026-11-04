-- Prove2me | solution 1 for ThreeSum.TernaryEnumeration.words_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:26:33.372216+00:00
-- url     : https://prove2.me/submissions/0b9cb9d3-cedd-4619-be61-dc668f56a061

import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Range
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryEnumeration
import Theorems.Thm_ThreeSum_TernaryEnumeration_zero_word_mem

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryEnumeration
namespace ThreeSum.TernaryEnumeration
theorem _root_.solution (n t : ℕ) : 0 < (words n t).length := by
  exact List.length_pos_of_mem (zero_word_mem n t)
end ThreeSum.TernaryEnumeration
