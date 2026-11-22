-- Prove2me | solution 1 for PebblingLean.Hypercube.HasHighDemandDistribution.mono_minPile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:50:24.044265+00:00
-- url     : https://prove2.me/submissions/b0d50b72-56b8-4197-b325-bee3822f44e9

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
theorem _root_.solution {n T costBound minPile minPile' : ℕ}
    (hminPile : minPile' ≤ minPile)
    (h : HasHighDemandDistribution n T costBound minPile) :
    HasHighDemandDistribution n T costBound minPile' := by
  rcases h with ⟨D, hsize, hsolv, hmin⟩
  exact ⟨D, hsize, hsolv, fun v hv => hminPile.trans (hmin v hv)⟩
end HasHighDemandDistribution
end PebblingLean.Hypercube
