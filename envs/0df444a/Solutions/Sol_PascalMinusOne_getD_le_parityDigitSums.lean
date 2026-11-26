-- Prove2me | solution 1 for PascalMinusOne.getD_le_parityDigitSums
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:21:26.476625+00:00
-- url     : https://prove2.me/submissions/7e3c0706-075d-4874-9572-7622925b9d20

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
theorem _root_.solution (L : List ℕ) (i : ℕ) :
    L.getD i 0 ≤
      if Even i then (parityDigitSums L).1 else (parityDigitSums L).2 := by
  induction L generalizing i with
  | nil =>
      simp [parityDigitSums]
  | cons d ds ih =>
      cases i with
      | zero =>
          simp [parityDigitSums]
      | succ i =>
          have h := ih i
          by_cases hi : Even i
          · simp [parityDigitSums, Nat.succ_eq_add_one, Nat.even_add_one, hi] at h ⊢
            exact h
          · simp [parityDigitSums, Nat.succ_eq_add_one, Nat.even_add_one, hi] at h ⊢
            omega
end PascalMinusOne
