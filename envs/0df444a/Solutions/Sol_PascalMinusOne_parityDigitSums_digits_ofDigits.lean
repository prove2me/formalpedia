-- Prove2me | solution 1 for PascalMinusOne.parityDigitSums_digits_ofDigits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:21:55.270297+00:00
-- url     : https://prove2.me/submissions/ca9fccb4-ded7-4481-8064-2253c04ed562

import Definitions.Def_PascalMinusOne_Basic
import Definitions.Def_PascalMinusOne_Digits
import Definitions.Def_PascalMinusOne_Kummer
import Definitions.Def_PascalMinusOne_SignedTokens
import Mathlib.Data.Nat.Digits.Div
import Mathlib.Data.List.GetD
import Definitions.Def_PascalMinusOne_MinusOne
import Theorems.Thm_PascalMinusOne_parityDigitSums_digitsAppend

set_option autoImplicit true
open PascalMinusOne
namespace PascalMinusOne
theorem _root_.solution {p : ℕ} (hp : 2 ≤ p) {L : List ℕ}
    (hL : ∀ d ∈ L, d < p) :
    parityDigitSums (Nat.digits p (Nat.ofDigits p L)) = parityDigitSums L := by
  have hinv :
      Nat.digitsAppend p L.length (Nat.ofDigits p L) = L :=
    (Nat.setInvOn_digitsAppend_ofDigits (by omega : 1 < p) L.length).1 ⟨rfl, hL⟩
  calc
    parityDigitSums (Nat.digits p (Nat.ofDigits p L)) =
        parityDigitSums (Nat.digitsAppend p L.length (Nat.ofDigits p L)) :=
      (parityDigitSums_digitsAppend p L.length (Nat.ofDigits p L)).symm
    _ = parityDigitSums L := congrArg parityDigitSums hinv
end PascalMinusOne
