-- Prove2me | solution 1 for PascalMinusOne.parityDigitSums_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:17:20.721622+00:00
-- url     : https://prove2.me/submissions/036a9b82-6cb7-40c2-9f2d-f894cd086ce8

import Mathlib.Data.Nat.Digits.Lemmas
import Definitions.Def_PascalMinusOne_Digits

set_option autoImplicit true
open PascalMinusOne
namespace PascalMinusOne
theorem _root_.solution (d : ℕ) (ds : List ℕ) :
    parityDigitSums (d :: ds) =
      (d + (parityDigitSums ds).2, (parityDigitSums ds).1) := rfl
end PascalMinusOne
