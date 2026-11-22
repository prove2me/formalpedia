-- Prove2me | solution 1 for PebblingLean.Pebbling.slice_canReachAtLeast_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:53:59.279882+00:00
-- url     : https://prove2.me/submissions/1a982457-e99c-4d1a-8ac1-fc746e631e1d

module
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Definitions.Def_LeanPool_PebblingLean_Product
public import Theorems.Thm_PebblingLean_Pebbling_fibersDistribution_apply
public import Theorems.Thm_PebblingLean_Pebbling_sliceDistribution_apply_on
public import Theorems.Thm_PebblingLean_Pebbling_sliceDistribution_apply_off
public import Theorems.Thm_PebblingLean_Pebbling_slice_reaches_right
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_from
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_of_ne
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_to
public import Theorems.Thm_PebblingLean_Pebbling_size_zero
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_from
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_of_ne
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_to
attribute [local simp] PebblingLean.Pebbling.size_zero


attribute [local simp] PebblingLean.Pebbling.fibersDistribution_apply
attribute [local simp] PebblingLean.Pebbling.sliceDistribution_apply_on
attribute [local simp] PebblingLean.Pebbling.sliceDistribution_apply_off

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
universe u v
open PebblingLean.Pebbling
variable {V : Type u} {W : Type v}
namespace PebblingLean.Pebbling
theorem _root_.solution [DecidableEq V] [DecidableEq W] {G : Graph V} {H : Graph W}
    {E : Pebbling W} {x : V} {target : W} {T : ℕ}
    (hcan : CanReachAtLeast H E target T) :
    CanReachAtLeast (Graph.cartesianProduct G H) (sliceDistribution x E) (x, target) T := by
  rcases hcan with ⟨F, hreach, htarget⟩
  exact ⟨sliceDistribution x F, slice_reaches_right (G := G) (H := H) (x := x) hreach, by
    simpa using htarget⟩
end PebblingLean.Pebbling
