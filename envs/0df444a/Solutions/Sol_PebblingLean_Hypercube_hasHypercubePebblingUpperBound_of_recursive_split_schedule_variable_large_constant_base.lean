-- Prove2me | solution 1 for PebblingLean.Hypercube.hasHypercubePebblingUpperBound_of_recursive_split_schedule_variable_large_constant_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:16:02.874661+00:00
-- url     : https://prove2.me/submissions/ece9072b-d068-4148-8c0f-0602daeaeacc

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability
public import Definitions.Def_LeanPool_PebblingLean_HypercubeProduct
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundRecurrence
public import Theorems.Thm_PebblingLean_Hypercube_hasHypercubePebblingUpperBound_of_highDemandDistribution
public import Theorems.Thm_PebblingLean_Hypercube_highDemandDistribution_of_recursive_split_schedule_variable_large_constant_base

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
namespace PebblingLean.Hypercube
theorem _root_.solution
    {costBound minPile splitA splitM K rIn rOut : ℕ → ℕ}
    {N : ℕ → ℕ → ℕ} {gap : ℕ → ℕ → ℝ} {n0 : ℕ}
    (hbase_minPile_pos :
      ∀ n : ℕ, n < n0 → 1 ≤ minPile n)
    (hbase_cost :
      ∀ n : ℕ, n < n0 → 2 ^ n * minPile n ≤ costBound n)
    (hsplit :
      ∀ n : ℕ, n0 ≤ n → splitA n + splitM n = n)
    (hsmaller :
      ∀ n : ℕ, n0 ≤ n → splitM n < n)
    (hgap_pos :
      ∀ n : ℕ, n0 ≤ n →
        ∀ t : ℕ, minPile (splitM n) ≤ t → 0 < gap n t)
    (hmean :
      ∀ n : ℕ, n0 ≤ n →
        ∀ t : ℕ, minPile (splitM n) ≤ t →
          (t : ℝ) + gap n t ≤
            (N n t : ℝ) * (annulusMean (splitA n) (rIn n) (rOut n) : ℝ))
    (hlog :
      ∀ n : ℕ, n0 ≤ n →
        ∀ t : ℕ, minPile (splitM n) ≤ t →
          ((splitA n + 1 : ℕ) : ℝ) * Real.log 2 ≤
            (gap n t) ^ 2 /
              (4 * (2 ^ (rOut n - rIn n) : ℝ) *
                ((N n t : ℝ) *
                  (annulusMean (splitA n) (rIn n) (rOut n) : ℝ))))
    (hfiberCost :
      ∀ n : ℕ, n0 ≤ n →
        ∀ t : ℕ, minPile (splitM n) ≤ t →
          N n t * 2 ^ rOut n ≤ t * K n)
    (hcost :
      ∀ n : ℕ, n0 ≤ n →
        costBound (splitM n) * K n ≤ costBound n)
    (hminPile :
      ∀ n : ℕ, n0 ≤ n →
        minPile n ≤ 2 ^ rOut n) :
    HasHypercubePebblingUpperBound costBound :=
  hasHypercubePebblingUpperBound_of_highDemandDistribution
    (highDemandDistribution_of_recursive_split_schedule_variable_large_constant_base
      (n0 := n0) hbase_minPile_pos hbase_cost hsplit hsmaller
      hgap_pos hmean hlog hfiberCost hcost hminPile)
end PebblingLean.Hypercube
