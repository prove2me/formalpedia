-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_recursiveCostBound_concreteSample_ceiling_finiteBase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:18:05.317195+00:00
-- url     : https://prove2.me/submissions/db2142da-2481-4d53-8947-21fff146432d

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_hasRealUpperBound_of_recursiveCostBound_concreteSample_ceiling_conditions
public import Theorems.Thm_PebblingLean_Hypercube_finiteBaseNormalizedBound_nonneg
public import Theorems.Thm_PebblingLean_Hypercube_normalizedCost_le_finiteBaseNormalizedBound_of_lt


set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters
namespace PebblingLean.Hypercube.PaperParameters
theorem _root_.solution
    {K A : ℝ} {n0 : ℕ}
    (hn0_pos : 0 < n0)
    (hquarter :
      ∀ n : ℕ, n0 ≤ n → 4 * splitM K n ≤ n)
    (hmean :
      ∀ n : ℕ, n0 ≤ n →
        ∀ t : ℕ, minPile (splitM K n) ≤ t →
          (t : ℝ) + demandGapForDemand n t ≤
            (sampleCountForDemand A K n t : ℝ) *
              (annulusMean (splitA K n) (rIn A K n) (rOut A K n) : ℝ))
    (hlog :
      ∀ n : ℕ, n0 ≤ n →
        ∀ t : ℕ, minPile (splitM K n) ≤ t →
          ((splitA K n + 1 : ℕ) : ℝ) * Real.log 2 ≤
            (demandGapForDemand n t) ^ 2 /
              (4 * (2 ^ (rOut A K n - rIn A K n) : ℝ) *
                ((sampleCountForDemand A K n t : ℝ) *
                  (annulusMean (splitA K n) (rIn A K n) (rOut A K n) : ℝ))))
    (hstack :
      ∀ n : ℕ, n0 ≤ n →
        ∀ t : ℕ, minPile (splitM K n) ≤ t →
          (2 ^ rOut A K n : ℝ) ≤
            (loss n / 2) * (t : ℝ) * (((4 : ℝ) / 3) ^ splitA K n))
    (hminExp :
      ∀ n : ℕ, n0 ≤ n → n / 5 ≤ rOut A K n)
    (hceilSlack :
      ∀ n : ℕ, n0 ≤ n →
        1 ≤ loss n * (((4 : ℝ) / 3) ^ splitA K n)) :
    HasRealHypercubePebblingUpperBound
      (Real.exp (4 * loss n0) *
        finiteBaseNormalizedBound (recursiveCostBound K n0) n0) :=
  hasRealUpperBound_of_recursiveCostBound_concreteSample_ceiling_conditions
    (K := K) (A := A) (n0 := n0)
    (B := finiteBaseNormalizedBound (recursiveCostBound K n0) n0)
    hn0_pos
    (finiteBaseNormalizedBound_nonneg (recursiveCostBound K n0) n0)
    (fun _n hn =>
      normalizedCost_le_finiteBaseNormalizedBound_of_lt
        (recursiveCostBound K n0) hn)
    hquarter hmean hlog hstack hminExp hceilSlack
end PebblingLean.Hypercube.PaperParameters
