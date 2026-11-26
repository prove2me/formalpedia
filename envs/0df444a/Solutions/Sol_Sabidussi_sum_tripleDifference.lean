-- Prove2me | solution 1 for Sabidussi.sum_tripleDifference
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:09:04.526467+00:00
-- url     : https://prove2.me/submissions/e43639b6-88c2-439c-99b7-caf338d83b2f

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Definitions.Def_Sabidussi_Color
import Theorems.Thm_Sabidussi_bracketRightHom_apply
import Theorems.Thm_Sabidussi_bracket_self
import Theorems.Thm_Sabidussi_tripleDifference_zero
import Theorems.Thm_Sabidussi_tripleDifference_one
import Theorems.Thm_Sabidussi_tripleDifference_two
attribute [local simp] Sabidussi.bracketRightHom_apply
attribute [local simp] Sabidussi.bracket_self
attribute [local simp] Sabidussi.tripleDifference_zero
attribute [local simp] Sabidussi.tripleDifference_one
attribute [local simp] Sabidussi.tripleDifference_two

set_option autoImplicit true
open Sabidussi
open scoped BigOperators
namespace Sabidussi
theorem _root_.solution (t : Color) : ∑ i, tripleDifference t i = 0 := by
  rw [Fin.sum_univ_three]
  change t + (t.2, t.1 + t.2) + (t.1 + t.2, t.1) = 0
  ext
  · change t.1 + t.2 + (t.1 + t.2) = 0
    exact F₂_add_self (t.1 + t.2)
  · change t.2 + (t.1 + t.2) + t.1 = 0
    calc
      t.2 + (t.1 + t.2) + t.1 = (t.1 + t.1) + (t.2 + t.2) := by abel
      _ = 0 := by simp
end Sabidussi
