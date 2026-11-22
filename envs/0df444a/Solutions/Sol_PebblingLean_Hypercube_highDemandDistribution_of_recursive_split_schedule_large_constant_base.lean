-- Prove2me | solution 1 for PebblingLean.Hypercube.highDemandDistribution_of_recursive_split_schedule_large_constant_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:15:16.944499+00:00
-- url     : https://prove2.me/submissions/8a895f32-eeb3-418a-a375-c5815f2b3c57

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability
public import Definitions.Def_LeanPool_PebblingLean_HypercubeProduct
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundRecurrence
public import Theorems.Thm_PebblingLean_Hypercube_hasHighDemandDistribution_constant_base_with_minPile
public import Theorems.Thm_PebblingLean_Hypercube_highDemandDistribution_of_recursive_split_schedule

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
namespace PebblingLean.Hypercube
theorem _root_.solution
    {costBound minPile splitA splitM K N rIn rOut : ℕ → ℕ}
    {gap : ℕ → ℝ} {n0 : ℕ}
    (hbase_minPile_pos :
      ∀ n : ℕ, n < n0 → 1 ≤ minPile n)
    (hbase_cost :
      ∀ n : ℕ, n < n0 → 2 ^ n * minPile n ≤ costBound n)
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
    ∀ n : ℕ, HasHighDemandDistribution n 1 (costBound n) (minPile n) :=
  highDemandDistribution_of_recursive_split_schedule
    (n0 := n0)
    (hbase := fun n hn =>
      hasHighDemandDistribution_constant_base_with_minPile
        (S := minPile n) (hbase_minPile_pos n hn)
        (hbase_cost n hn) le_rfl)
    hsplit hsmaller hgap_pos hmean hlog hfiberCost hcost hminPile
end PebblingLean.Hypercube
