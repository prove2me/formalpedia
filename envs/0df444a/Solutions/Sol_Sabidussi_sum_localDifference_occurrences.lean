-- Prove2me | solution 1 for Sabidussi.sum_localDifference_occurrences
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:11:47.795879+00:00
-- url     : https://prove2.me/submissions/6f2566e1-4b07-4f21-b394-521f5eb18bcf

import Definitions.Def_Sabidussi_Color
import Definitions.Def_Sabidussi_LocalPattern
import Theorems.Thm_Sabidussi_localDifference_zero
import Theorems.Thm_Sabidussi_localDifference_one
import Theorems.Thm_Sabidussi_bracketRightHom_apply
import Theorems.Thm_Sabidussi_bracket_self
import Theorems.Thm_Sabidussi_sum_doubleDifference
import Theorems.Thm_Sabidussi_sum_tripleDifference
import Theorems.Thm_Sabidussi_tripleDifference_one
import Theorems.Thm_Sabidussi_tripleDifference_two
import Theorems.Thm_Sabidussi_tripleDifference_zero
attribute [local simp] Sabidussi.bracketRightHom_apply
attribute [local simp] Sabidussi.bracket_self
attribute [local simp] Sabidussi.tripleDifference_one
attribute [local simp] Sabidussi.tripleDifference_two
attribute [local simp] Sabidussi.tripleDifference_zero


attribute [local simp] Sabidussi.localDifference_zero
attribute [local simp] Sabidussi.localDifference_one

set_option autoImplicit true
open Sabidussi
open scoped BigOperators
namespace Sabidussi
theorem _root_.solution (n : ℕ) (c : Fin 3) :
    ∑ i, localDifference n c i = 0 := by
  induction n using Nat.twoStepInduction with
  | zero => exact sum_doubleDifference (choiceColor c)
  | one => exact sum_tripleDifference (choiceColor c)
  | more n ih _ =>
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
      simp only [localDifference, Fin.cases_zero, Fin.cases_succ]
      calc
        choiceColor c + (choiceColor c + ∑ i, localDifference n c i) =
            (choiceColor c + choiceColor c) + ∑ i, localDifference n c i := by abel
        _ = 0 := by rw [color_add_self, zero_add, ih]
end Sabidussi
