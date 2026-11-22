-- Prove2me | solution 1 for PebblingLean.Hypercube.hasHighDemandDistribution_constant_base_with_minPile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:54:51.304037+00:00
-- url     : https://prove2.me/submissions/dc5dd0cf-c82d-47f5-936a-275eaba804c6

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability
public import Definitions.Def_LeanPool_PebblingLean_HypercubeProduct
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundRecurrence
public import Theorems.Thm_PebblingLean_Hypercube_hasHighDemandDistribution_constant
public import Theorems.Thm_PebblingLean_Pebbling_solvableAtLeast_mono


set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
namespace PebblingLean.Hypercube
theorem _root_.solution
    {n S costBound minPile : ℕ}
    (hS : 1 ≤ S)
    (hcost : 2 ^ n * S ≤ costBound)
    (hminPile : minPile ≤ S) :
    HasHighDemandDistribution n 1 costBound minPile := by
  rcases hasHighDemandDistribution_constant n S with ⟨D, hDsize, hDsolv, hDmin⟩
  exact ⟨D, hDsize.trans hcost, Pebbling.solvableAtLeast_mono hS hDsolv,
    fun v hv => hminPile.trans (hDmin v hv)⟩
end PebblingLean.Hypercube
