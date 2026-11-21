-- Prove2me | solution 1 for RungeKuttaOrderConditions.Butcher.rk4_order4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:59:24.693672+00:00
-- url     : https://prove2.me/submissions/9b1a9655-62f7-42df-9acd-d8af244ca85a

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
public import Theorems.Thm_RungeKuttaOrderConditions_Butcher_satisfiesOrderConditions_iff
section
@[expose] public section
namespace RungeKuttaOrderConditions
namespace Q15
end Q15
namespace Z15
end Z15
namespace Butcher
end Butcher
end RungeKuttaOrderConditions
namespace RungeKuttaOrderConditions.Butcher
end Butcher
end RungeKuttaOrderConditions
namespace RungeKuttaOrderConditions.Butcher
variable {K : Type*} [CommRing K]
end Butcher
end RungeKuttaOrderConditions
namespace RungeKuttaOrderConditions.Butcher
variable {K : Type*} [CommRing K]
end Butcher
end RungeKuttaOrderConditions
namespace RungeKuttaOrderConditions.Butcher
variable {K : Type*} [CommRing K]
private theorem catalogFourEq : catalog 4 = treesUpToFour := rfl
end Butcher
end RungeKuttaOrderConditions
end
end

set_option autoImplicit true
@[expose] public section
public section
open RungeKuttaOrderConditions RungeKuttaOrderConditions.Butcher
variable {K : Type*} [CommRing K]
namespace RungeKuttaOrderConditions.Butcher
theorem _root_.solution : satisfiesOrderConditions rk4A rk4B 4 := by
  rw [satisfiesOrderConditions_iff, catalogFourEq]
  decide +kernel
end RungeKuttaOrderConditions.Butcher
