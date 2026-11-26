-- Prove2me | solution 1 for Sabidussi.quadratic_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:09:01.178231+00:00
-- url     : https://prove2.me/submissions/e11a2c09-2aed-4ac5-b9f1-c2311b578fe6

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Definitions.Def_Sabidussi_Color
import Theorems.Thm_Sabidussi_bracketRightHom_apply
import Theorems.Thm_Sabidussi_bracket_self
attribute [local simp] Sabidussi.bracketRightHom_apply
attribute [local simp] Sabidussi.bracket_self

set_option autoImplicit true
open Sabidussi
open scoped BigOperators
namespace Sabidussi
theorem _root_.solution (x y : Color) :
    quadratic (x + y) = quadratic x + quadratic y + bracket x y := by
  simp only [quadratic, bracket, Prod.fst_add, Prod.snd_add]
  ring
end Sabidussi
