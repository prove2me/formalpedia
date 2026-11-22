-- Prove2me | solution 1 for PebblingLean.Pebbling.canReachAtLeast_of_walk_of_single_dominated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:14:01.319843+00:00
-- url     : https://prove2.me/submissions/db2c1878-637f-40fb-bb17-790fc15708a6

module
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_PebblingLean_Delivery
public import Theorems.Thm_PebblingLean_Pebbling_canReachAtLeast_single_of_walk
public import Theorems.Thm_PebblingLean_Pebbling_canReachAtLeast_of_dominates


set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
universe u
open PebblingLean.Pebbling
variable {V : Type u}
namespace PebblingLean.Pebbling
theorem _root_.solution [DecidableEq V] {G : Graph V}
    {D : Pebbling V} {u target : V} (walk : G.Walk u target) {T : ℕ}
    (hdom : Dominates D (single u (T * 2 ^ walk.length))) :
    CanReachAtLeast G D target T :=
  canReachAtLeast_of_dominates (canReachAtLeast_single_of_walk walk T) hdom
end PebblingLean.Pebbling
