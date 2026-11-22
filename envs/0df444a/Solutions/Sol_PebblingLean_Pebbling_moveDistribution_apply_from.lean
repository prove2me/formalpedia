-- Prove2me | solution 1 for PebblingLean.Pebbling.moveDistribution_apply_from
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:47:50.438612+00:00
-- url     : https://prove2.me/submissions/5f804e93-fac9-43a0-ba02-2473d0f66536

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Theorems.Thm_PebblingLean_Pebbling_size_zero
attribute [local simp] PebblingLean.Pebbling.size_zero

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
universe u
open PebblingLean.Pebbling
variable {V : Type u}
namespace PebblingLean.Pebbling
theorem _root_.solution [DecidableEq V] (D : Pebbling V) {u v : V} :
    moveDistribution D u v u = D u - 2 := by
  simp [moveDistribution]
end PebblingLean.Pebbling
