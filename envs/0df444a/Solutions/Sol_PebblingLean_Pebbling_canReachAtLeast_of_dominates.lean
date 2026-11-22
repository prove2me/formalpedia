-- Prove2me | solution 1 for PebblingLean.Pebbling.canReachAtLeast_of_dominates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:53:40.50864+00:00
-- url     : https://prove2.me/submissions/59cc7b7b-2e04-4002-9adc-4db316faf59a

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Theorems.Thm_PebblingLean_Pebbling_reaches_of_dominates

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
universe u
open PebblingLean.Pebbling
variable {V : Type u}
namespace PebblingLean.Pebbling
theorem _root_.solution [DecidableEq V] {G : Graph V} {D D' : Pebbling V}
    {target : V} {T : ℕ} (hcan : CanReachAtLeast G D target T) (hdom : Dominates D' D) :
    CanReachAtLeast G D' target T := by
  rcases hcan with ⟨E, hreach, htarget⟩
  rcases reaches_of_dominates hreach hdom with ⟨E', hreach', hdom_E⟩
  exact ⟨E', hreach', htarget.trans (hdom_E target)⟩
end PebblingLean.Pebbling
