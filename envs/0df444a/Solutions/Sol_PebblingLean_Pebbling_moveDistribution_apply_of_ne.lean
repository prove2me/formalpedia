-- Prove2me | solution 1 for PebblingLean.Pebbling.moveDistribution_apply_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:49:02.77681+00:00
-- url     : https://prove2.me/submissions/b2fb99a0-23a1-4cb9-9c70-5cdefea5ed8e

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Theorems.Thm_PebblingLean_Pebbling_size_zero
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_from
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_to
attribute [local simp] PebblingLean.Pebbling.size_zero
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_from
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_to

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
universe u
open PebblingLean.Pebbling
variable {V : Type u}
namespace PebblingLean.Pebbling
theorem _root_.solution [DecidableEq V] (D : Pebbling V) {u v x : V}
    (hxu : x ≠ u) (hxv : x ≠ v) :
    moveDistribution D u v x = D x := by
  simp [moveDistribution, hxu, hxv]
end PebblingLean.Pebbling
