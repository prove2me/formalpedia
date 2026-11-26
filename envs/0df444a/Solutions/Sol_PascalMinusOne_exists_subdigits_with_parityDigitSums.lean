-- Prove2me | solution 1 for PascalMinusOne.exists_subdigits_with_parityDigitSums
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:20:33.831059+00:00
-- url     : https://prove2.me/submissions/7542e7e4-b0b1-4e28-a01c-0996c4a79972

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
theorem _root_.solution
    (D : List ℕ) {a b : ℕ}
    (ha : a ≤ (parityDigitSums D).1)
    (hb : b ≤ (parityDigitSums D).2) :
    ∃ S : List ℕ,
      List.Forall₂ (· ≤ ·) S D ∧ parityDigitSums S = (a, b) := by
  induction D generalizing a b with
  | nil =>
      simp [parityDigitSums] at ha hb
      have ha0 : a = 0 := by omega
      have hb0 : b = 0 := by omega
      subst a
      subst b
      exact ⟨[], List.Forall₂.nil, rfl⟩
  | cons d D ih =>
      simp only [parityDigitSums_cons, Prod.fst, Prod.snd] at ha hb
      by_cases had : a ≤ d
      · obtain ⟨T, hT, hpar⟩ :=
          ih (a := b) (b := 0) hb (Nat.zero_le _)
        refine ⟨a :: T, List.Forall₂.cons had hT, ?_⟩
        simp [parityDigitSums, hpar]
      · have hda : d < a := Nat.lt_of_not_ge had
        have htail : a - d ≤ (parityDigitSums D).2 := by omega
        obtain ⟨T, hT, hpar⟩ := ih (a := b) (b := a - d) hb htail
        refine ⟨d :: T, List.Forall₂.cons (Nat.le_refl d) hT, ?_⟩
        simp [parityDigitSums, hpar]
        omega
end PascalMinusOne
