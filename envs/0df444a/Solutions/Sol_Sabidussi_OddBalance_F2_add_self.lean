-- Prove2me | solution 1 for Sabidussi.OddBalance.F2.add_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:12:03.294836+00:00
-- url     : https://prove2.me/submissions/8ea24fc8-d44d-4da1-9502-539ab438f556

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Prod
import Definitions.Def_Sabidussi_OddBalance

set_option autoImplicit true
open scoped BigOperators
open Finset
open Sabidussi
open Sabidussi.OddBalance
namespace Sabidussi.OddBalance
namespace F2
theorem _root_.solution (a : F2) : a + a = 0 := by
  fin_cases a <;> decide
end F2
end Sabidussi.OddBalance
