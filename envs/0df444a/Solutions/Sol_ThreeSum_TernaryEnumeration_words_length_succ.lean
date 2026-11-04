-- Prove2me | solution 1 for ThreeSum.TernaryEnumeration.words_length_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:24:53.852205+00:00
-- url     : https://prove2.me/submissions/d747c078-f5f6-47a7-a8b8-7d30a6bde77d

import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Range
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryEnumeration
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryEnumeration
namespace ThreeSum.TernaryEnumeration
theorem _root_.solution (n t : ℕ) :
    (words (n + 1) t).length =
      ((digits t).map fun d => (words n (t - d)).length).sum := by
  simp [words, List.length_flatMap]
end ThreeSum.TernaryEnumeration
