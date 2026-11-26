-- Prove2me | solution 1 for PascalMinusOne.digitAt_ofDigits_eq_getD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:21:29.333724+00:00
-- url     : https://prove2.me/submissions/cdab0ab1-f825-4e4a-a799-bce4c6eb2f50

import Definitions.Def_PascalMinusOne_Basic
import Definitions.Def_PascalMinusOne_Digits
import Definitions.Def_PascalMinusOne_Kummer
import Definitions.Def_PascalMinusOne_SignedTokens
import Mathlib.Data.Nat.Digits.Div
import Mathlib.Data.List.GetD
import Definitions.Def_PascalMinusOne_MinusOne
import Theorems.Thm_PascalMinusOne_head_drop_eq_getD
import Theorems.Thm_PascalMinusOne_evenDigitSum_zero
import Theorems.Thm_PascalMinusOne_mem_admissibleIndices_iff
import Theorems.Thm_PascalMinusOne_oddDigitSum_zero
import Theorems.Thm_PascalMinusOne_parityDigitSums_cons
import Theorems.Thm_PascalMinusOne_parityDigitSums_nil
import Theorems.Thm_PascalMinusOne_signedZeroSum_m_zero
import Theorems.Thm_PascalMinusOne_signedZeroSum_one_one
import Theorems.Thm_PascalMinusOne_signedZeroSum_zero_m
attribute [local simp] PascalMinusOne.evenDigitSum_zero
attribute [local simp] PascalMinusOne.mem_admissibleIndices_iff
attribute [local simp] PascalMinusOne.oddDigitSum_zero
attribute [local simp] PascalMinusOne.parityDigitSums_cons
attribute [local simp] PascalMinusOne.parityDigitSums_nil
attribute [local simp] PascalMinusOne.signedZeroSum_m_zero
attribute [local simp] PascalMinusOne.signedZeroSum_one_one
attribute [local simp] PascalMinusOne.signedZeroSum_zero_m



set_option autoImplicit true
open PascalMinusOne
namespace PascalMinusOne
theorem _root_.solution {p i : ℕ} (hp : 2 ≤ p) (L : List ℕ)
    (hL : ∀ d ∈ L, d < p) :
    digitAt p (Nat.ofDigits p L) i = L.getD i 0 := by
  rw [digitAt, Nat.ofDigits_div_pow_eq_ofDigits_drop i (by omega) L hL,
    Nat.ofDigits_mod_eq_head!]
  have hhead : (L.drop i).head! < p := by
    by_cases hnil : L.drop i = []
    · simpa [hnil] using (show 0 < p by omega)
    · exact hL _ (List.mem_of_mem_drop (List.head!_mem_self hnil))
  rw [Nat.mod_eq_of_lt hhead, head_drop_eq_getD]
end PascalMinusOne
