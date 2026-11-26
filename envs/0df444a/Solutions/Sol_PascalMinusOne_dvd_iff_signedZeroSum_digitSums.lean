-- Prove2me | solution 1 for PascalMinusOne.dvd_iff_signedZeroSum_digitSums
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:21:04.344965+00:00
-- url     : https://prove2.me/submissions/dcf8b61f-838e-4a11-84ca-9af4b638d6c7

import Definitions.Def_PascalMinusOne_Basic
import Definitions.Def_PascalMinusOne_Digits
import Definitions.Def_PascalMinusOne_Kummer
import Definitions.Def_PascalMinusOne_SignedTokens
import Mathlib.Data.Nat.Digits.Div
import Mathlib.Data.List.GetD
import Definitions.Def_PascalMinusOne_MinusOne
import Theorems.Thm_PascalMinusOne_ofDigits_neg_one_eq_parityDigitSums
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
theorem _root_.solution {m p k : ℕ}
    (hm : 2 ≤ m) (hpm : p % m = m - 1) :
    m ∣ k ↔ SignedZeroSum m (evenDigitSum p k) (oddDigitSum p k) := by
  have hpmod : p ≡ m - 1 [MOD m] := by
    rw [Nat.ModEq, Nat.mod_eq_of_lt (by omega : m - 1 < m)]
    exact hpm
  have hmp1 : m ∣ p + 1 := by
    rw [← Nat.modEq_zero_iff_dvd]
    have h := hpmod.add_right 1
    simpa [Nat.ModEq, Nat.sub_add_cancel (by omega : 1 ≤ m)] using h
  have hdiv : (m : ℤ) ∣ (p : ℤ) - (-1 : ℤ) := by
    rw [sub_neg_eq_add]
    exact_mod_cast hmp1
  simpa [SignedZeroSum, evenDigitSum, oddDigitSum,
    ofDigits_neg_one_eq_parityDigitSums] using
    (Nat.dvd_iff_dvd_ofDigits m p (-1 : ℤ) hdiv k)
end PascalMinusOne
