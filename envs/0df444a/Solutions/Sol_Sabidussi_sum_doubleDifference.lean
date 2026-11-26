-- Prove2me | solution 1 for Sabidussi.sum_doubleDifference
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:11:10.395471+00:00
-- url     : https://prove2.me/submissions/d5ef5b50-8fb5-4a4e-a2d3-6a48ff5c5dc2

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Definitions.Def_Sabidussi_Color

set_option autoImplicit true
open Sabidussi
open scoped BigOperators
namespace Sabidussi
theorem _root_.solution (t : Color) : ∑ i, doubleDifference t i = 0 := by
  rw [Fin.sum_univ_two]
  exact color_add_self t
end Sabidussi
