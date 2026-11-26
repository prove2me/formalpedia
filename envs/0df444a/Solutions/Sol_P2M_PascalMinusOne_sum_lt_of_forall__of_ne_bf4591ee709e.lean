-- Prove2me | solution 1 for P2M_PascalMinusOne_sum_lt_of_forall__of_ne_bf4591ee709e
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:21:25.583559+00:00
-- url     : https://prove2.me/submissions/603befc0-dce9-4312-aa9a-146f43f0b405

import Definitions.Def_PascalMinusOne_Basic
import Definitions.Def_PascalMinusOne_Digits
import Definitions.Def_PascalMinusOne_Kummer
import Definitions.Def_PascalMinusOne_SignedTokens
import Mathlib.Data.Nat.Digits.Div
import Mathlib.Data.List.GetD
import Definitions.Def_PascalMinusOne_MinusOne
import Theorems.Thm_P2M_PascalMinusOne_sum_le_of_forall__a2453d65e7c8
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
    (h : List.Forall₂ (· ≤ ·) S D) (hne : S ≠ D) :
    S.sum < D.sum := by
  induction h with
  | nil => exact (hne rfl).elim
  | @cons s d S D hsd htail ih =>
      simp only [List.sum_cons]
      by_cases hsdEq : s = d
      · subst d
        have htailNe : S ≠ D := by
          intro hEq
          apply hne
          simp [hEq]
        exact Nat.add_lt_add_left (ih htailNe) s
      · have hslt : s < d := lt_of_le_of_ne hsd hsdEq
        have hsum : S.sum ≤ D.sum := sum_le_of_forall₂ htail
        omega
end PascalMinusOne
