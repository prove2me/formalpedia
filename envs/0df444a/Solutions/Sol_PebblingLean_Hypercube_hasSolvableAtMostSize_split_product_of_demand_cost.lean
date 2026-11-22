-- Prove2me | solution 1 for PebblingLean.Hypercube.hasSolvableAtMostSize_split_product_of_demand_cost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:06:45.067276+00:00
-- url     : https://prove2.me/submissions/b90ca0ed-8eec-4549-b533-07b172f827bf

module
public import Definitions.Def_LeanPool_PebblingLean_GraphIso
public import Definitions.Def_LeanPool_PebblingLean_Product
public import Definitions.Def_LeanPool_PebblingLean_UpperBound
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finite.Prod
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_PebblingLean_HypercubeProduct
public import Theorems.Thm_PebblingLean_Hypercube_hasSolvableAtMostSize_split_product_of_fiber_demands

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
namespace PebblingLean.Hypercube
theorem _root_.solution
    {a m : ℕ} {E : Pebbling (HypercubeVertex m)} {demandCost : ℕ → ℕ}
    (hE : Pebbling.Solvable (graph m) E)
    (hcost :
      ∀ T : ℕ, T ≠ 0 →
        Pebbling.HasSolvableAtMostSize (graph a) T (demandCost T)) :
    Pebbling.HasSolvableAtMostSize (graph (a + m)) 1
      (∑ z : HypercubeVertex m, if E z = 0 then 0 else demandCost (E z)) := by
  classical
  exact hasSolvableAtMostSize_split_product_of_fiber_demands
    (a := a) (m := m) (E := E)
    (cost := fun z : HypercubeVertex m => demandCost (E z))
    hE (fun z hz => hcost (E z) hz)
end PebblingLean.Hypercube
