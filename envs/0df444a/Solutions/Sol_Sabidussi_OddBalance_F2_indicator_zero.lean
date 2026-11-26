-- Prove2me | solution 1 for Sabidussi.OddBalance.F2.indicator_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:11:53.40861+00:00
-- url     : https://prove2.me/submissions/0139a111-9bf7-4617-8833-7ffa6415dd46

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
theorem _root_.solution (a : F2) : (if a = 0 then 1 else 0) = 1 + a := by
  fin_cases a <;> decide
end F2
end Sabidussi.OddBalance
