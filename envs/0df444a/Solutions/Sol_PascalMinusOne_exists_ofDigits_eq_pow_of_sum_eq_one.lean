-- Prove2me | solution 1 for PascalMinusOne.exists_ofDigits_eq_pow_of_sum_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:21:33.780852+00:00
-- url     : https://prove2.me/submissions/0406f74b-5230-4caa-9934-2adc8d3fc299

import Definitions.Def_PascalMinusOne_Basic
import Definitions.Def_PascalMinusOne_Digits
import Definitions.Def_PascalMinusOne_Kummer
import Definitions.Def_PascalMinusOne_SignedTokens
import Mathlib.Data.Nat.Digits.Div
import Mathlib.Data.List.GetD
import Definitions.Def_PascalMinusOne_MinusOne
import Theorems.Thm_PascalMinusOne_ofDigits_eq_zero_of_sum_eq_zero
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
theorem _root_.solution (p : ℕ) :
    ∀ L : List ℕ, L.sum = 1 →
      ∃ i, i < L.length ∧ Nat.ofDigits p L = p ^ i := by
  intro L
  induction L with
  | nil =>
      intro hsum
      simp at hsum
  | cons d ds ih =>
      intro hsum
      simp only [List.sum_cons] at hsum
      by_cases hd : d = 0
      · subst d
        have htail : ds.sum = 1 := by omega
        obtain ⟨i, hi, hpow⟩ := ih htail
        refine ⟨i + 1, by simp; omega, ?_⟩
        simp only [Nat.ofDigits_cons, zero_add, hpow]
        rw [Nat.mul_comm]
        exact (pow_succ p i).symm
      · have hd1 : d = 1 := by
          have hdpos : 0 < d := Nat.pos_of_ne_zero hd
          omega
        have htail : ds.sum = 0 := by omega
        have hzero : Nat.ofDigits p ds = 0 :=
          ofDigits_eq_zero_of_sum_eq_zero p ds htail
        subst d
        refine ⟨0, by simp, ?_⟩
        simp [Nat.ofDigits_cons, hzero]
end PascalMinusOne
