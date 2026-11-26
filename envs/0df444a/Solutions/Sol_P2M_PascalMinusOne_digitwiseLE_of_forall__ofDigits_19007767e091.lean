-- Prove2me | solution 1 for P2M_PascalMinusOne_digitwiseLE_of_forall__ofDigits_19007767e091
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:22:28.342047+00:00
-- url     : https://prove2.me/submissions/0282b953-1e0b-407f-9992-3639c7255d8d

import Definitions.Def_PascalMinusOne_Basic
import Definitions.Def_PascalMinusOne_Digits
import Definitions.Def_PascalMinusOne_Kummer
import Definitions.Def_PascalMinusOne_SignedTokens
import Mathlib.Data.Nat.Digits.Div
import Mathlib.Data.List.GetD
import Definitions.Def_PascalMinusOne_MinusOne
import Theorems.Thm_PascalMinusOne_digitAt_ofDigits_eq_getD
import Theorems.Thm_P2M_PascalMinusOne_getD_le_of_forall__67768b8a94b6

set_option autoImplicit true
open PascalMinusOne
namespace PascalMinusOne
theorem _root_.solution {p : ℕ} (hp : 2 ≤ p) {S D : List ℕ}
    (hSD : List.Forall₂ (· ≤ ·) S D)
    (hS : ∀ s ∈ S, s < p)
    (hD : ∀ d ∈ D, d < p) :
    DigitwiseLE p (Nat.ofDigits p S) (Nat.ofDigits p D) := by
  intro i
  rw [digitAt_ofDigits_eq_getD hp S hS, digitAt_ofDigits_eq_getD hp D hD]
  exact getD_le_of_forall₂ hSD i
end PascalMinusOne
