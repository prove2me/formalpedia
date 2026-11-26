-- Prove2me | solution 1 for Sabidussi.sum_bracket_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:07:47.633222+00:00
-- url     : https://prove2.me/submissions/702811d9-8793-40f1-941a-8d2241a54e2c

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Definitions.Def_Sabidussi_Color

set_option autoImplicit true
open Sabidussi
open scoped BigOperators
namespace Sabidussi
theorem _root_.solution {I : Type*} [Fintype I] (x : Color) (f : I → Color) :
    ∑ i, bracket x (f i) = bracket x (∑ i, f i) := by
  change ∑ i, bracketRightHom x (f i) = bracketRightHom x (∑ i, f i)
  exact (map_sum (bracketRightHom x) f Finset.univ).symm
end Sabidussi
