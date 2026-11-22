-- Prove2me | solution 1 for PebblingLean.Hypercube.hasSolvableAtMostSize_split_product_of_fiber_demands
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:05:57.197899+00:00
-- url     : https://prove2.me/submissions/2756a22d-3d47-432f-b052-be2c9f3aac48

module
public import Definitions.Def_LeanPool_PebblingLean_GraphIso
public import Definitions.Def_LeanPool_PebblingLean_Product
public import Definitions.Def_LeanPool_PebblingLean_UpperBound
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finite.Prod
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_PebblingLean_HypercubeProduct
public import Theorems.Thm_PebblingLean_GraphIso_map_hasSolvableAtMostSize
public import Theorems.Thm_PebblingLean_Pebbling_hasSolvableAtMostSize_product_of_fiber_demands


set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
namespace PebblingLean.Hypercube
theorem _root_.solution
    {a m : ℕ} {E : Pebbling (HypercubeVertex m)}
    {cost : HypercubeVertex m → ℕ}
    (hE : Pebbling.Solvable (graph m) E)
    (hcost :
      ∀ z : HypercubeVertex m,
        E z ≠ 0 → Pebbling.HasSolvableAtMostSize (graph a) (E z) (cost z)) :
    Pebbling.HasSolvableAtMostSize (graph (a + m)) 1
      (∑ z : HypercubeVertex m, if E z = 0 then 0 else cost z) := by
  classical
  have hprod :
      Pebbling.HasSolvableAtMostSize
        (Graph.cartesianProduct (graph a) (graph m)) 1
        (∑ z : HypercubeVertex m, if E z = 0 then 0 else cost z) :=
    Pebbling.hasSolvableAtMostSize_product_of_fiber_demands
      (G := graph a) (H := graph m) hE hcost
  exact (splitGraphIso a m).symm.map_hasSolvableAtMostSize hprod
end PebblingLean.Hypercube
