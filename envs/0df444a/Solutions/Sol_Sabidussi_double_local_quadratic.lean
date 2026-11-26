-- Prove2me | solution 1 for Sabidussi.double_local_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:15:38.710136+00:00
-- url     : https://prove2.me/submissions/b3ce2933-154d-43f9-b4b7-445111fc8011

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
theorem _root_.solution (t : Color) :
    (∑ i, quadratic (doubleDifference t i)) +
      (∑ i, ∑ j,
        if j < i then bracket (doubleDifference t i) (doubleDifference t j) else 0) = 0 := by
  simp only [Fin.sum_univ_two, doubleDifference, quadratic, bracket]
  norm_num
  ring_nf
  rw [show (2 : F₂) = 0 from ZMod.natCast_self 2]
  simp
end Sabidussi
