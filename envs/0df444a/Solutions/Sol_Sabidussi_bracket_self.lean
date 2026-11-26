-- Prove2me | solution 1 for Sabidussi.bracket_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:08:24.228062+00:00
-- url     : https://prove2.me/submissions/d2a59ff2-bd5f-4f95-8df2-82835621b886

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Definitions.Def_Sabidussi_Color
import Theorems.Thm_Sabidussi_bracketRightHom_apply
attribute [local simp] Sabidussi.bracketRightHom_apply

set_option autoImplicit true
open Sabidussi
open scoped BigOperators
namespace Sabidussi
theorem _root_.solution (x : Color) : bracket x x = 0 := by
  simp [bracket, mul_comm]
end Sabidussi
