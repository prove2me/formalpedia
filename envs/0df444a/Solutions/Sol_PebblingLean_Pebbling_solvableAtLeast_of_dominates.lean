-- Prove2me | solution 1 for PebblingLean.Pebbling.solvableAtLeast_of_dominates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:13:57.459896+00:00
-- url     : https://prove2.me/submissions/28934ab7-1ba8-445c-b4a0-e73b0a12cbad

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Theorems.Thm_PebblingLean_Pebbling_canReachAtLeast_of_dominates

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
universe u
open PebblingLean.Pebbling
variable {V : Type u}
namespace PebblingLean.Pebbling
theorem _root_.solution [DecidableEq V] {G : Graph V} {D D' : Pebbling V}
    {T : ℕ} (hsolv : SolvableAtLeast G D T) (hdom : Dominates D' D) :
    SolvableAtLeast G D' T := by
  intro target
  exact canReachAtLeast_of_dominates (hsolv target) hdom
end PebblingLean.Pebbling
