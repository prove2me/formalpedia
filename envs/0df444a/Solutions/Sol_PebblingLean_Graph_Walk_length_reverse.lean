-- Prove2me | solution 1 for PebblingLean.Graph.Walk.length_reverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:49:57.250546+00:00
-- url     : https://prove2.me/submissions/85ddd166-fd22-402f-a3af-d37ddb5c735a

module
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_PebblingLean_Delivery
public import Theorems.Thm_PebblingLean_Graph_Walk_length_append
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_from
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_of_ne
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_to
public import Theorems.Thm_PebblingLean_Pebbling_size_zero
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_from
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_of_ne
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_to
attribute [local simp] PebblingLean.Pebbling.size_zero


attribute [local simp] PebblingLean.Graph.Walk.length_append

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
universe u
open PebblingLean.Graph
variable {V : Type u} (G : Graph V)
open PebblingLean.Graph.Walk
namespace PebblingLean.Graph.Walk
theorem _root_.solution {u v : V} (p : G.Walk u v) :
    p.reverse.length = p.length := by
  induction p with
  | nil _ =>
      rfl
  | cons _ tail ih =>
      simp [reverse, length, ih]
end PebblingLean.Graph.Walk
