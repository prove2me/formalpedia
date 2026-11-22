-- Prove2me | solution 1 for PebblingLean.Hypercube.HasHighDemandDistribution.to_ordinary_hasSolvableAtMostSize
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:14:04.412266+00:00
-- url     : https://prove2.me/submissions/ef5f2346-036e-44fe-aa6f-d8592b057c98

module
public import Definitions.Def_LeanPool_PebblingLean_Hypercube
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_PebblingLean_UpperBound
public import Theorems.Thm_PebblingLean_Hypercube_HasHighDemandDistribution_to_hasSolvableAtMostSize
public import Theorems.Thm_PebblingLean_Pebbling_hasSolvableAtMostSize_mono_demand


set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open Pebbling
namespace PebblingLean.Hypercube
namespace HasHighDemandDistribution
theorem _root_.solution
    {n T costBound minPile : ℕ} (hT : 1 ≤ T)
    (h : HasHighDemandDistribution n T costBound minPile) :
    HasSolvableAtMostSize (graph n) 1 costBound :=
  Pebbling.hasSolvableAtMostSize_mono_demand hT h.to_hasSolvableAtMostSize
end HasHighDemandDistribution
end PebblingLean.Hypercube
