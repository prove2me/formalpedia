-- Prove2me | solution 1 for PebblingLean.Pebbling.solvableAtLeast_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:47:53.464032+00:00
-- url     : https://prove2.me/submissions/b64f4b14-9c90-413c-88a7-e7809975f58b

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Theorems.Thm_PebblingLean_Pebbling_canReachAtLeast_zero

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
universe u
open PebblingLean.Pebbling
variable {V : Type u}
namespace PebblingLean.Pebbling
theorem _root_.solution [DecidableEq V] (G : Graph V) (D : Pebbling V) :
    SolvableAtLeast G D 0 := by
  intro target
  exact canReachAtLeast_zero G D target
end PebblingLean.Pebbling
