-- Prove2me | solution 1 for PebblingLean.Pebbling.moveDistribution_apply_to
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:48:29.995928+00:00
-- url     : https://prove2.me/submissions/70eb7693-3635-4277-815c-ceb25d60031a

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Theorems.Thm_PebblingLean_Pebbling_size_zero
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_from
attribute [local simp] PebblingLean.Pebbling.size_zero
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_from

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
universe u
open PebblingLean.Pebbling
variable {V : Type u}
namespace PebblingLean.Pebbling
theorem _root_.solution [DecidableEq V] (D : Pebbling V) {u v : V} (h : v ≠ u) :
    moveDistribution D u v v = D v + 1 := by
  simp [moveDistribution, h]
end PebblingLean.Pebbling
