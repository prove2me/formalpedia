-- Prove2me | solution 1 for PascalMinusOne.parityDigitSums_append_replicate_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:20:17.464812+00:00
-- url     : https://prove2.me/submissions/a4ff3244-04cd-4a58-947c-b91dd50fab98

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
theorem _root_.solution (L : List ℕ) (n : ℕ) :
    parityDigitSums (L ++ List.replicate n 0) = parityDigitSums L := by
  have hzero : ∀ r : ℕ, parityDigitSums (List.replicate r 0) = (0, 0) := by
    intro r
    induction r with
    | zero => rfl
    | succ r ih => simp [List.replicate_succ, parityDigitSums, ih]
  induction L with
  | nil => simpa using hzero n
  | cons d ds ih =>
      simp only [List.cons_append, parityDigitSums_cons, ih]
end PascalMinusOne
