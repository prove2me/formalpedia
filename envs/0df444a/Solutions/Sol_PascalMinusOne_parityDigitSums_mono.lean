-- Prove2me | solution 1 for PascalMinusOne.parityDigitSums_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:20:28.635558+00:00
-- url     : https://prove2.me/submissions/8cf37897-4bad-4fbe-9edc-8ee413c5269b

import Definitions.Def_PascalMinusOne_Basic
import Definitions.Def_PascalMinusOne_Digits
import Definitions.Def_PascalMinusOne_Kummer
import Definitions.Def_PascalMinusOne_SignedTokens
import Mathlib.Data.Nat.Digits.Div
import Mathlib.Data.List.GetD
import Definitions.Def_PascalMinusOne_MinusOne
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
theorem _root_.solution {S D : List ℕ}
    (h : List.Forall₂ (· ≤ ·) S D) :
    (parityDigitSums S).1 ≤ (parityDigitSums D).1 ∧
      (parityDigitSums S).2 ≤ (parityDigitSums D).2 := by
  induction h with
  | nil => simp [parityDigitSums]
  | @cons s d S D hsd htail ih =>
      simp only [parityDigitSums_cons, Prod.fst, Prod.snd]
      omega
end PascalMinusOne
