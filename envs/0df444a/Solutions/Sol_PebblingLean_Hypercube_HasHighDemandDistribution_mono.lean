-- Prove2me | solution 1 for PebblingLean.Hypercube.HasHighDemandDistribution.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:51:24.290478+00:00
-- url     : https://prove2.me/submissions/b2c7844c-43e8-4681-8e20-4972a89e3b82

module
public import Definitions.Def_LeanPool_PebblingLean_Hypercube
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_PebblingLean_UpperBound
public import Theorems.Thm_PebblingLean_Hypercube_HasHighDemandDistribution_mono_cost
public import Theorems.Thm_PebblingLean_Hypercube_HasHighDemandDistribution_mono_minPile

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open Pebbling
namespace PebblingLean.Hypercube
namespace HasHighDemandDistribution
theorem _root_.solution
    {n T costBound costBound' minPile minPile' : ℕ}
    (hcost : costBound ≤ costBound') (hminPile : minPile' ≤ minPile)
    (h : HasHighDemandDistribution n T costBound minPile) :
    HasHighDemandDistribution n T costBound' minPile' :=
  (h.mono_cost hcost).mono_minPile hminPile
end HasHighDemandDistribution
end PebblingLean.Hypercube
