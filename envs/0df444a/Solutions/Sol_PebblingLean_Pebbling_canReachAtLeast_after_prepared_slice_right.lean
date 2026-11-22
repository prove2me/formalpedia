-- Prove2me | solution 1 for PebblingLean.Pebbling.canReachAtLeast_after_prepared_slice_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:03:35.103604+00:00
-- url     : https://prove2.me/submissions/fcee703f-a2ec-4fa0-8c91-c6054b1cbeac

module
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Definitions.Def_LeanPool_PebblingLean_Product
public import Theorems.Thm_PebblingLean_Pebbling_canReachAtLeast_of_dominates_slice_right

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
universe u v
open PebblingLean.Pebbling
variable {V : Type u} {W : Type v}
namespace PebblingLean.Pebbling
theorem _root_.solution [DecidableEq V] [DecidableEq W]
    {G : Graph V} {H : Graph W} {D Dprep : Pebbling (V × W)} {E : Pebbling W}
    {x : V} {target : W} {T : ℕ}
    (hprepReach : Reaches (Graph.cartesianProduct G H) D Dprep)
    (hprepDom : Dominates Dprep (sliceDistribution x E))
    (hcan : CanReachAtLeast H E target T) :
    CanReachAtLeast (Graph.cartesianProduct G H) D (x, target) T := by
  rcases canReachAtLeast_of_dominates_slice_right (G := G) (H := H)
      (D := Dprep) (E := E) (x := x) hprepDom hcan with
    ⟨Dfinish, hfinishReach, htarget⟩
  exact ⟨Dfinish, Relation.ReflTransGen.trans hprepReach hfinishReach, htarget⟩
end PebblingLean.Pebbling
