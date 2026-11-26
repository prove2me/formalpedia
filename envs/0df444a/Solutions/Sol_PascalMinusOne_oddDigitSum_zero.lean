-- Prove2me | solution 1 for PascalMinusOne.oddDigitSum_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:18:17.290815+00:00
-- url     : https://prove2.me/submissions/1db9763b-9aea-474d-b8de-054ccffb7578

import Mathlib.Data.Nat.Digits.Lemmas
import Definitions.Def_PascalMinusOne_Digits
import Theorems.Thm_PascalMinusOne_parityDigitSums_nil
import Theorems.Thm_PascalMinusOne_parityDigitSums_cons
import Theorems.Thm_PascalMinusOne_evenDigitSum_zero
attribute [local simp] PascalMinusOne.parityDigitSums_nil
attribute [local simp] PascalMinusOne.parityDigitSums_cons
attribute [local simp] PascalMinusOne.evenDigitSum_zero

set_option autoImplicit true
open PascalMinusOne
namespace PascalMinusOne
theorem _root_.solution (p : ℕ) : oddDigitSum p 0 = 0 := by
  simp [oddDigitSum]
end PascalMinusOne
