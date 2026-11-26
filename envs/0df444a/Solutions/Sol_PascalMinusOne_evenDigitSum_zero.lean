-- Prove2me | solution 1 for PascalMinusOne.evenDigitSum_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:17:48.746106+00:00
-- url     : https://prove2.me/submissions/f19f67f2-0e5e-4ea5-a4f6-3ef782c798d9

import Mathlib.Data.Nat.Digits.Lemmas
import Definitions.Def_PascalMinusOne_Digits
import Theorems.Thm_PascalMinusOne_parityDigitSums_nil
import Theorems.Thm_PascalMinusOne_parityDigitSums_cons
attribute [local simp] PascalMinusOne.parityDigitSums_nil
attribute [local simp] PascalMinusOne.parityDigitSums_cons

set_option autoImplicit true
open PascalMinusOne
namespace PascalMinusOne
theorem _root_.solution (p : ℕ) : evenDigitSum p 0 = 0 := by
  simp [evenDigitSum]
end PascalMinusOne
