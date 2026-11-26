-- Prove2me | solution 1 for Sabidussi.sum_tripleDifference_choice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:11:50.85823+00:00
-- url     : https://prove2.me/submissions/fe86eb08-9400-4615-9c7c-a17d4983f941

import Definitions.Def_Sabidussi_Color
import Definitions.Def_Sabidussi_LocalPattern
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



set_option autoImplicit true
open Sabidussi
open scoped BigOperators
namespace Sabidussi
theorem _root_.solution (i : Fin 3) :
    ∑ c, tripleDifference (choiceColor c) i = 0 := by
  fin_cases i <;>
    simp [Fin.sum_univ_three, choiceColor, tripleDifference, Prod.ext_iff]
end Sabidussi
