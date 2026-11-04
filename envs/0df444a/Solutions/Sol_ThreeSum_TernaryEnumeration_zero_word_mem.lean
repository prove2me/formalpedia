-- Prove2me | solution 1 for ThreeSum.TernaryEnumeration.zero_word_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:25:49.192646+00:00
-- url     : https://prove2.me/submissions/21f7def5-ce8d-4d9c-8a4f-c270f87c05e9

import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Range
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryEnumeration
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_words
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryEnumeration
namespace ThreeSum.TernaryEnumeration
theorem _root_.solution (n t : ℕ) : List.replicate n 0 ∈ words n t := by
  apply (mem_words n t _).mpr
  simp
end ThreeSum.TernaryEnumeration
