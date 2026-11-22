-- Prove2me | solution 1 for PebblingLean.Graph.Walk.length_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:49:28.141723+00:00
-- url     : https://prove2.me/submissions/d44840fe-d7d1-4319-8d8d-fa35c443a145

module
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_PebblingLean_Delivery
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_from
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_of_ne
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_to
public import Theorems.Thm_PebblingLean_Pebbling_size_zero
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_from
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_of_ne
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_to
attribute [local simp] PebblingLean.Pebbling.size_zero



set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
universe u
open PebblingLean.Graph
variable {V : Type u} (G : Graph V)
open PebblingLean.Graph.Walk
namespace PebblingLean.Graph.Walk
theorem _root_.solution {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    (Graph.Walk.append G p q).length = p.length + q.length := by
  induction p generalizing w with
  | nil _ =>
      simp [append, length]
  | cons _ tail ih =>
      simp [append, length, ih, Nat.add_assoc, Nat.add_comm]
end PebblingLean.Graph.Walk
