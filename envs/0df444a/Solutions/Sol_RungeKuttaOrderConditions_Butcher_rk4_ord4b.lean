-- Prove2me | solution 1 for RungeKuttaOrderConditions.Butcher.rk4_ord4b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:59:08.875335+00:00
-- url     : https://prove2.me/submissions/b960d620-4e8b-42f2-9dd6-39bd0ae9d4d3

module
public import Mathlib.Algebra.Ring.Rat
public meta import Mathlib.Tactic.Basic
public meta import Mathlib.Tactic.ToAdditive
public meta import Mathlib.Tactic.ToDual
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_RungeKuttaOrderConditions_ButcherOrder

set_option autoImplicit true
@[expose] public section
public section
open RungeKuttaOrderConditions RungeKuttaOrderConditions.Butcher
variable {K : Type*} [CommRing K]
namespace RungeKuttaOrderConditions.Butcher
theorem _root_.solution : orderCond rk4A rk4B t42 := by decide +kernel
end RungeKuttaOrderConditions.Butcher
