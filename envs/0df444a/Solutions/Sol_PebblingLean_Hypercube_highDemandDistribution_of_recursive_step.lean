-- Prove2me | solution 1 for PebblingLean.Hypercube.highDemandDistribution_of_recursive_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:54:50.828865+00:00
-- url     : https://prove2.me/submissions/ae698140-fca3-4390-bf76-ab5c50210846

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability
public import Definitions.Def_LeanPool_PebblingLean_HypercubeProduct
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundRecurrence

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
namespace PebblingLean.Hypercube
theorem _root_.solution
    {costBound minPile : ℕ → ℕ} {n0 : ℕ}
    (hbase :
      ∀ n : ℕ, n < n0 →
        HasHighDemandDistribution n 1 (costBound n) (minPile n))
    (hstep :
      ∀ n : ℕ, n0 ≤ n →
        (∀ m : ℕ, m < n →
          HasHighDemandDistribution m 1 (costBound m) (minPile m)) →
        HasHighDemandDistribution n 1 (costBound n) (minPile n)) :
    ∀ n : ℕ, HasHighDemandDistribution n 1 (costBound n) (minPile n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n < n0
      · exact hbase n hn
      · exact hstep n (Nat.le_of_not_gt hn) ih
end PebblingLean.Hypercube
