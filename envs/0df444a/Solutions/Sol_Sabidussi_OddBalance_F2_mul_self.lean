-- Prove2me | solution 1 for Sabidussi.OddBalance.F2.mul_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:11:58.006888+00:00
-- url     : https://prove2.me/submissions/d143b135-90be-4fd2-b98a-2a66738a1b71

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
theorem _root_.solution (a : F2) : a * a = a := by
  revert a
  decide
end F2
end Sabidussi.OddBalance
