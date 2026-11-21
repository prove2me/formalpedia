-- Prove2me | solution 1 for RungeKuttaOrderConditions.Butcher.gauss_order6
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:58:51.276921+00:00
-- url     : https://prove2.me/submissions/692ca89d-fb5e-4c4d-bacb-a830a1f81c77

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
public import Theorems.Thm_RungeKuttaOrderConditions_Butcher_satisfiesOrderConditionsInt_iff

set_option autoImplicit true
@[expose] public section
public section
open RungeKuttaOrderConditions RungeKuttaOrderConditions.Butcher
variable {K : Type*} [CommRing K]
namespace RungeKuttaOrderConditions.Butcher
theorem _root_.solution : satisfiesOrderConditionsInt gaussIA gaussIB Dscale 6 := by
  rw [satisfiesOrderConditionsInt_iff]
  decide +kernel
end RungeKuttaOrderConditions.Butcher
