-- Prove2me | solution 1 for PebblingLean.Pebbling.solvableAtLeast_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:47:55.373027+00:00
-- url     : https://prove2.me/submissions/9a1e859c-286f-498c-874f-1a6963a159cb

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Theorems.Thm_PebblingLean_Pebbling_canReachAtLeast_mono

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
universe u
open PebblingLean.Pebbling
variable {V : Type u}
namespace PebblingLean.Pebbling
theorem _root_.solution [DecidableEq V] {G : Graph V} {D : Pebbling V}
    {T T' : ℕ} (hTT' : T' ≤ T) (hsolv : SolvableAtLeast G D T) :
    SolvableAtLeast G D T' := by
  intro target
  exact canReachAtLeast_mono hTT' (hsolv target)
end PebblingLean.Pebbling
