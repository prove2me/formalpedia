-- Prove2me | solution 1 for PebblingLean.Hypercube.HasHighDemandDistribution.to_hasSolvableAtMostSize
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:51:22.705391+00:00
-- url     : https://prove2.me/submissions/ef1c7e77-855a-4c6e-9260-241b123f7e29

module
public import Definitions.Def_LeanPool_PebblingLean_Hypercube
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_PebblingLean_UpperBound

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open Pebbling
namespace PebblingLean.Hypercube
namespace HasHighDemandDistribution
theorem _root_.solution
    {n T costBound minPile : ℕ}
    (h : HasHighDemandDistribution n T costBound minPile) :
    HasSolvableAtMostSize (graph n) T costBound := by
  rcases h with ⟨D, hsize, hsolv, _hmin⟩
  exact ⟨D, hsize, hsolv⟩
end HasHighDemandDistribution
end PebblingLean.Hypercube
