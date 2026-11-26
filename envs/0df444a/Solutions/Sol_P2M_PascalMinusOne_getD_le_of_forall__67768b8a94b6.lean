-- Prove2me | solution 1 for P2M_PascalMinusOne_getD_le_of_forall__67768b8a94b6
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:21:22.117003+00:00
-- url     : https://prove2.me/submissions/e116b38e-cb10-47bd-b7d5-e855fc5edae9

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
    (h : List.Forall₂ (· ≤ ·) S D) (i : ℕ) :
    S.getD i 0 ≤ D.getD i 0 := by
  induction h generalizing i with
  | nil => simp
  | @cons s d S D hsd htail ih =>
      cases i with
      | zero => simpa using hsd
      | succ i => simpa using ih i
end PascalMinusOne
