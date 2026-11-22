-- Prove2me | solution 1 for PebblingLean.Pebbling.canReachAtLeast_of_dominates_slice_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:54:40.036892+00:00
-- url     : https://prove2.me/submissions/8dfbebb4-9ee4-4448-8e3a-e58b52181392

module
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Definitions.Def_LeanPool_PebblingLean_Product
public import Theorems.Thm_PebblingLean_Pebbling_slice_canReachAtLeast_right
public import Theorems.Thm_PebblingLean_Pebbling_canReachAtLeast_of_dominates


set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
universe u v
open PebblingLean.Pebbling
variable {V : Type u} {W : Type v}
namespace PebblingLean.Pebbling
theorem _root_.solution [DecidableEq V] [DecidableEq W]
    {G : Graph V} {H : Graph W} {D : Pebbling (V × W)} {E : Pebbling W}
    {x : V} {target : W} {T : ℕ}
    (hdom : Dominates D (sliceDistribution x E))
    (hcan : CanReachAtLeast H E target T) :
    CanReachAtLeast (Graph.cartesianProduct G H) D (x, target) T :=
  canReachAtLeast_of_dominates
    (slice_canReachAtLeast_right (G := G) (H := H) (x := x) hcan) hdom
end PebblingLean.Pebbling
