-- Prove2me | solution 1 for RungeKuttaOrderConditions.Butcher.satisfiesOrderConditions_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:57:44.826665+00:00
-- url     : https://prove2.me/submissions/22dd5735-4470-4ba6-beb4-07812f78a487

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
theorem _root_.solution (A : List (List K)) (b : List K) (p : Nat) :
    satisfiesOrderConditions A b p ↔ ∀ t ∈ catalog p, orderCond A b t := by
  constructor
  · intro h t ht
    exact h t (of_decide_eq_true (List.mem_filter.1 ht).2)
  · intro h t hle
    exact h t (List.mem_filter.2 ⟨mem_build_trees p t hle, decide_eq_true hle⟩)
end RungeKuttaOrderConditions.Butcher
