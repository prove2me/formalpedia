-- Prove2me | solution 1 for P2M_PascalMinusOne_all_lt_of_forall__le_eb2ba6507b45
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:19:39.101405+00:00
-- url     : https://prove2.me/submissions/3e77749d-22be-4453-b098-5dffd29b436c

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
theorem _root_.solution {S D : List ℕ} {p : ℕ}
    (h : List.Forall₂ (· ≤ ·) S D)
    (hD : ∀ d ∈ D, d < p) :
    ∀ s ∈ S, s < p := by
  revert hD
  induction h with
  | nil => simp
  | @cons s d S D hsd htail ih =>
      intro hD x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact lt_of_le_of_lt hsd (hD d List.mem_cons_self)
      · exact ih (fun y hy => hD y (List.mem_cons_of_mem d hy)) x hx
end PascalMinusOne
