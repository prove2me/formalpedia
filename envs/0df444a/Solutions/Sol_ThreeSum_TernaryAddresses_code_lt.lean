-- Prove2me | solution 1 for ThreeSum.TernaryAddresses.code_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:25:50.10759+00:00
-- url     : https://prove2.me/submissions/f343493d-2c9d-4a73-a559-6a45214a4680

import Definitions.Def_Submission_ThreeSum_TernaryEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Theorems.Thm_ThreeSum_TernaryAddresses_digitCode_le
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits



set_option autoImplicit false
open ThreeSum ThreeSum.TernaryAddresses
open ThreeSum.TernaryEnumeration
namespace ThreeSum.TernaryAddresses
theorem _root_.solution (xs : List ℕ) (h : ∀ d ∈ xs, d < 3) : code xs < 4 ^ xs.length := by
  induction xs with
  | nil => simp [code]
  | cons d xs ih =>
    have hd := digitCode_le (h d (by simp))
    have hx := ih (fun e he => h e (by simp [he]))
    have hp : 0 < 4 ^ xs.length := by positivity
    simp only [code, List.length_cons, pow_succ]
    nlinarith
end ThreeSum.TernaryAddresses
