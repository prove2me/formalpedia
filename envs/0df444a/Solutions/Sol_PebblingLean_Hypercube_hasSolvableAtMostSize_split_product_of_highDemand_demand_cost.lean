-- Prove2me | solution 1 for PebblingLean.Hypercube.hasSolvableAtMostSize_split_product_of_highDemand_demand_cost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:14:07.814164+00:00
-- url     : https://prove2.me/submissions/3e61979f-064a-44b8-86c6-f0e8f265b085

module
public import Definitions.Def_LeanPool_PebblingLean_GraphIso
public import Definitions.Def_LeanPool_PebblingLean_Product
public import Definitions.Def_LeanPool_PebblingLean_UpperBound
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finite.Prod
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_PebblingLean_HypercubeProduct
public import Theorems.Thm_PebblingLean_Hypercube_hasSolvableAtMostSize_split_product_of_demand_cost
public import Theorems.Thm_PebblingLean_Pebbling_solvable_of_solvableAtLeast


set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
namespace PebblingLean.Hypercube
theorem _root_.solution
    {a m T : ℕ} {E : Pebbling (HypercubeVertex m)} {demandCost : ℕ → ℕ}
    (hT : 1 ≤ T)
    (hE : Pebbling.SolvableAtLeast (graph m) E T)
    (hcost :
      ∀ t : ℕ, t ≠ 0 →
        Pebbling.HasSolvableAtMostSize (graph a) t (demandCost t)) :
    Pebbling.HasSolvableAtMostSize (graph (a + m)) 1
      (∑ z : HypercubeVertex m, if E z = 0 then 0 else demandCost (E z)) :=
  hasSolvableAtMostSize_split_product_of_demand_cost
    (a := a) (m := m) (E := E) (demandCost := demandCost)
    (Pebbling.solvable_of_solvableAtLeast hT hE) hcost
end PebblingLean.Hypercube
