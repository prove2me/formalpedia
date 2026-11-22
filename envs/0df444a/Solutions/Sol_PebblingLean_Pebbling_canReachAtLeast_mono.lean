-- Prove2me | solution 1 for PebblingLean.Pebbling.canReachAtLeast_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:46:35.021784+00:00
-- url     : https://prove2.me/submissions/347f7bde-14ab-4be0-9eba-75dd336cc0d9

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_PebblingLean_Basic

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
universe u
open PebblingLean.Pebbling
variable {V : Type u}
namespace PebblingLean.Pebbling
theorem _root_.solution [DecidableEq V] {G : Graph V} {D : Pebbling V}
    {target : V} {T T' : ℕ} (hTT' : T' ≤ T)
    (hcan : CanReachAtLeast G D target T) :
    CanReachAtLeast G D target T' := by
  rcases hcan with ⟨E, hreach, htarget⟩
  exact ⟨E, hreach, hTT'.trans htarget⟩
end PebblingLean.Pebbling
