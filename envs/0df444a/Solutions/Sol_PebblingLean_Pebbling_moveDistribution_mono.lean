-- Prove2me | solution 1 for PebblingLean.Pebbling.moveDistribution_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:49:30.98311+00:00
-- url     : https://prove2.me/submissions/5d449f8d-82eb-424c-9ef5-3fa695c56030

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Theorems.Thm_PebblingLean_Pebbling_size_zero
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_from
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_to
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_of_ne
attribute [local simp] PebblingLean.Pebbling.size_zero
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_from
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_to
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_of_ne

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
universe u
open PebblingLean.Pebbling
variable {V : Type u}
namespace PebblingLean.Pebbling
theorem _root_.solution [DecidableEq V] {D D' : Pebbling V} {u v : V}
    (huv : u ≠ v) (hdom : Dominates D' D) :
    Dominates (moveDistribution D' u v) (moveDistribution D u v) := by
  intro x
  by_cases hxu : x = u
  · subst x
    simpa [moveDistribution] using Nat.sub_le_sub_right (hdom u) 2
  · by_cases hxv : x = v
    · subst x
      have hvu : v ≠ u := fun h => huv h.symm
      simpa [moveDistribution, hvu] using hdom v
    · simpa [moveDistribution, hxu, hxv] using hdom x
end PebblingLean.Pebbling
