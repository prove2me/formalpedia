-- Prove2me | solution 1 for PascalMinusOne.parityDigitSums_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:17:19.66164+00:00
-- url     : https://prove2.me/submissions/107ed99f-7c6e-4a8e-8883-55be10eedce9

import Mathlib.Data.Nat.Digits.Lemmas
import Definitions.Def_PascalMinusOne_Digits

set_option autoImplicit true
open PascalMinusOne
namespace PascalMinusOne
theorem _root_.solution : parityDigitSums [] = (0, 0) := rfl
end PascalMinusOne
