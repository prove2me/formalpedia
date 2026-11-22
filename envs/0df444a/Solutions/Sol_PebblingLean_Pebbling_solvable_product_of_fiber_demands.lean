-- Prove2me | solution 1 for PebblingLean.Pebbling.solvable_product_of_fiber_demands
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:04:20.512783+00:00
-- url     : https://prove2.me/submissions/43841086-6ba6-4551-adbe-c61d96d1cc03

module
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Definitions.Def_LeanPool_PebblingLean_Product
public import Theorems.Thm_PebblingLean_Pebbling_canReachAtLeast_after_prepared_slice_right
public import Theorems.Thm_PebblingLean_Pebbling_fibers_prepare_slice_right

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
universe u v
open PebblingLean.Pebbling
variable {V : Type u} {W : Type v}
namespace PebblingLean.Pebbling
theorem _root_.solution [Finite W] [DecidableEq V] [DecidableEq W]
    {G : Graph V} {H : Graph W} {E : Pebbling W} {F : W → Pebbling V}
    (hE : Solvable H E)
    (hF : ∀ z : W, SolvableAtLeast G (F z) (E z)) :
    Solvable (Graph.cartesianProduct G H) (fibersDistribution F) := by
  intro target
  rcases target with ⟨x, y⟩
  rcases fibers_prepare_slice_right (G := G) (H := H) (E := E) (F := F) (x := x)
      (fun z => hF z x) with
    ⟨Dprep, hprepReach, hprepDom⟩
  exact canReachAtLeast_after_prepared_slice_right (G := G) (H := H)
    (D := fibersDistribution F) (Dprep := Dprep) (E := E) (x := x) (target := y)
    hprepReach hprepDom (hE y)
end PebblingLean.Pebbling
