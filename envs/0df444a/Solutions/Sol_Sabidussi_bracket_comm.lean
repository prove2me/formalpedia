-- Prove2me | solution 1 for Sabidussi.bracket_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:08:24.716884+00:00
-- url     : https://prove2.me/submissions/2cca24f9-b495-4720-9ef5-48b78ed0b0d6

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Definitions.Def_Sabidussi_Color
import Theorems.Thm_Sabidussi_bracketRightHom_apply
attribute [local simp] Sabidussi.bracketRightHom_apply

set_option autoImplicit true
open Sabidussi
open scoped BigOperators
namespace Sabidussi
theorem _root_.solution (x y : Color) : bracket x y = bracket y x := by
  simp [bracket, add_comm, mul_comm]
end Sabidussi
