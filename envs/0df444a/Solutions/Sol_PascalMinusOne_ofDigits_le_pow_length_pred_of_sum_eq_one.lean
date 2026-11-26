-- Prove2me | solution 1 for PascalMinusOne.ofDigits_le_pow_length_pred_of_sum_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:21:30.18943+00:00
-- url     : https://prove2.me/submissions/b676c705-5c45-46c1-963a-bda3dfe03adb

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
theorem _root_.solution {p : ℕ} (hp : 0 < p) :
    ∀ L : List ℕ, L.sum = 1 →
      Nat.ofDigits p L ≤ p ^ (L.length - 1) := by
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
        have hdsne : ds ≠ [] := by
          intro hnil
          subst ds
          simp at htail
        have hlen : 1 ≤ ds.length :=
          List.length_pos_iff_ne_nil.mpr hdsne
        have hih := ih htail
        simp only [Nat.ofDigits_cons, zero_add, List.length_cons]
        calc
          p * Nat.ofDigits p ds ≤ p * p ^ (ds.length - 1) :=
            Nat.mul_le_mul_left p hih
          _ = p ^ (ds.length - 1) * p := by rw [Nat.mul_comm]
          _ = p ^ ((ds.length - 1) + 1) := (pow_succ p (ds.length - 1)).symm
          _ = p ^ ds.length := by rw [Nat.sub_add_cancel hlen]
      · have hd1 : d = 1 := by
          have hdpos : 0 < d := Nat.pos_of_ne_zero hd
          omega
        have htail : ds.sum = 0 := by omega
        have hofd : Nat.ofDigits p ds = 0 :=
          ofDigits_eq_zero_of_sum_eq_zero p ds htail
        subst d
        simp only [Nat.ofDigits_cons, hofd, mul_zero, add_zero, List.length_cons]
        exact pow_pos hp ds.length
end PascalMinusOne
