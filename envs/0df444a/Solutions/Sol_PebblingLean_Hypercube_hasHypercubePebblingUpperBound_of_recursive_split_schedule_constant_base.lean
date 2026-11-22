-- Prove2me | solution 1 for PebblingLean.Hypercube.hasHypercubePebblingUpperBound_of_recursive_split_schedule_constant_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:15:59.930011+00:00
-- url     : https://prove2.me/submissions/54c0ba25-f9c1-4d0f-818d-6de532f2d4f0

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability
public import Definitions.Def_LeanPool_PebblingLean_HypercubeProduct
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundRecurrence
public import Theorems.Thm_PebblingLean_Hypercube_hasHypercubePebblingUpperBound_of_highDemandDistribution
public import Theorems.Thm_PebblingLean_Hypercube_highDemandDistribution_of_recursive_split_schedule_constant_base

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
namespace PebblingLean.Hypercube
theorem _root_.solution
    {costBound minPile splitA splitM K N rIn rOut : ℕ → ℕ}
    {gap : ℕ → ℝ} {n0 : ℕ}
    (hbase_cost :
      ∀ n : ℕ, n < n0 → 2 ^ n ≤ costBound n)
    (hbase_minPile :
      ∀ n : ℕ, n < n0 → minPile n ≤ 1)
    (hsplit :
      ∀ n : ℕ, n0 ≤ n → splitA n + splitM n = n)
    (hsmaller :
      ∀ n : ℕ, n0 ≤ n → splitM n < n)
    (hgap_pos :
      ∀ n : ℕ, n0 ≤ n → 0 < gap n)
    (hmean :
      ∀ n : ℕ, n0 ≤ n →
        (costBound (splitM n) : ℝ) + gap n ≤
          (N n : ℝ) * (annulusMean (splitA n) (rIn n) (rOut n) : ℝ))
    (hlog :
      ∀ n : ℕ, n0 ≤ n →
        ((splitA n + 1 : ℕ) : ℝ) * Real.log 2 ≤
          (gap n) ^ 2 /
            (4 * (2 ^ (rOut n - rIn n) : ℝ) *
              ((N n : ℝ) *
                (annulusMean (splitA n) (rIn n) (rOut n) : ℝ))))
    (hfiberCost :
      ∀ n : ℕ, n0 ≤ n →
        N n * 2 ^ rOut n ≤ minPile (splitM n) * K n)
    (hcost :
      ∀ n : ℕ, n0 ≤ n →
        costBound (splitM n) * K n ≤ costBound n)
    (hminPile :
      ∀ n : ℕ, n0 ≤ n →
        minPile n ≤ 2 ^ rOut n) :
    HasHypercubePebblingUpperBound costBound :=
  hasHypercubePebblingUpperBound_of_highDemandDistribution
    (highDemandDistribution_of_recursive_split_schedule_constant_base
      (n0 := n0) hbase_cost hbase_minPile hsplit hsmaller hgap_pos
      hmean hlog hfiberCost hcost hminPile)
end PebblingLean.Hypercube
