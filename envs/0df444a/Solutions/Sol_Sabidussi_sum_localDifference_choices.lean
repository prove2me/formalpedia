-- Prove2me | solution 1 for Sabidussi.sum_localDifference_choices
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:12:31.691101+00:00
-- url     : https://prove2.me/submissions/99215cb1-cf8e-4c33-83c9-82ecb20b42dc

import Definitions.Def_Sabidussi_Color
import Definitions.Def_Sabidussi_LocalPattern
import Theorems.Thm_Sabidussi_sum_choiceColor
import Theorems.Thm_Sabidussi_sum_tripleDifference_choice
import Theorems.Thm_Sabidussi_localDifference_zero
import Theorems.Thm_Sabidussi_localDifference_one
import Theorems.Thm_Sabidussi_bracketRightHom_apply
import Theorems.Thm_Sabidussi_bracket_self
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
theorem _root_.solution (n : ℕ) (i : Fin (n + 2)) :
    ∑ c, localDifference n c i = 0 := by
  induction n using Nat.twoStepInduction with
  | zero => simpa [doubleDifference] using sum_choiceColor
  | one => exact sum_tripleDifference_choice i
  | more n ih _ =>
      refine Fin.cases ?_ (fun j ↦ Fin.cases ?_ (fun k ↦ ih k) j) i
      · exact sum_choiceColor
      · exact sum_choiceColor
end Sabidussi
