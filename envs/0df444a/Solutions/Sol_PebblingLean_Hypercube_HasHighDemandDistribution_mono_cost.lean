-- Prove2me | solution 1 for PebblingLean.Hypercube.HasHighDemandDistribution.mono_cost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:50:23.3941+00:00
-- url     : https://prove2.me/submissions/7801f1b6-5a91-41a9-84a5-5eaa35719f0b

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
theorem _root_.solution {n T costBound costBound' minPile : ℕ}
    (hcost : costBound ≤ costBound')
    (h : HasHighDemandDistribution n T costBound minPile) :
    HasHighDemandDistribution n T costBound' minPile := by
  rcases h with ⟨D, hsize, hsolv, hmin⟩
  exact ⟨D, hsize.trans hcost, hsolv, hmin⟩
end HasHighDemandDistribution
end PebblingLean.Hypercube
