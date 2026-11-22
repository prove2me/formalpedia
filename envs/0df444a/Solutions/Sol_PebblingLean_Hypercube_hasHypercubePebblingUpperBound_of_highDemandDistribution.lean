-- Prove2me | solution 1 for PebblingLean.Hypercube.hasHypercubePebblingUpperBound_of_highDemandDistribution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:54:44.780422+00:00
-- url     : https://prove2.me/submissions/3f882264-a92b-466b-b09b-ad0679ab5d4b

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability
public import Definitions.Def_LeanPool_PebblingLean_HypercubeProduct
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundRecurrence
public import Theorems.Thm_PebblingLean_Hypercube_HasHighDemandDistribution_to_hasSolvableAtMostSize


set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
namespace PebblingLean.Hypercube
theorem _root_.solution
    {costBound minPile : ℕ → ℕ}
    (h : ∀ n : ℕ, HasHighDemandDistribution n 1 (costBound n) (minPile n)) :
    HasHypercubePebblingUpperBound costBound := by
  intro n
  exact (h n).to_hasSolvableAtMostSize
end PebblingLean.Hypercube
