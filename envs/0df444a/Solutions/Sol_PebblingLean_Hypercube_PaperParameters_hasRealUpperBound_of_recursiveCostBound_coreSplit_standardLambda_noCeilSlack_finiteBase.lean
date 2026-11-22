-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_recursiveCostBound_coreSplit_standardLambda_noCeilSlack_finiteBase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:46:57.091801+00:00
-- url     : https://prove2.me/submissions/c8bef9f8-8c01-435a-b0d1-5f4eeb8f59c8

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_splitM_real_le_quarter_of_ceiling_bound
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_hasRealUpperBound_of_recursiveCostBound_standardLambda_noCeilSlack_finiteBase

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
    (hn0_growth : 58 ≤ n0)
    (hsplitCore_nonneg :
      ∀ n : ℕ, n0 ≤ n →
        0 ≤ K * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)))
    (hsplitCore :
      ∀ n : ℕ, n0 ≤ n →
        K * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) + 1 ≤
          (n : ℝ) / 4)
    (hleftMul :
      ∀ n : ℕ, n0 ≤ n →
        16 * leftChernoffTerm A K (annulusChernoffLambda A K) n ≤ loss n)
    (hrightMul :
      ∀ n : ℕ, n0 ≤ n →
        16 * rightChernoffTerm A K (annulusChernoffLambda A K) n ≤ loss n)
    (hlogWidthMul :
      ∀ n : ℕ, n0 ≤ n →
        128 * (2 ^ (2 * annulusWidth A K n) : ℝ) *
            (((splitA K n + 1 : ℕ) : ℝ) * Real.log 2) ≤
          (loss n) ^ 2 * (minPile (splitM K n) : ℝ))
    (hstackMul :
      ∀ n : ℕ, n0 ≤ n →
        2 * ((n : ℝ) ^ 2) * (2 ^ rOut A K n : ℝ) ≤
          (minPile (splitM K n) : ℝ) *
            (((4 : ℝ) / 3) ^ splitA K n)) :
    HasRealHypercubePebblingUpperBound
      (Real.exp (4 * loss n0) *
        finiteBaseNormalizedBound (recursiveCostBound K n0) n0) :=
  hasRealUpperBound_of_recursiveCostBound_standardLambda_noCeilSlack_finiteBase
    (K := K) (A := A) (n0 := n0)
    hn0_pos
    hn0_growth
    (fun n hn =>
      splitM_real_le_quarter_of_ceiling_bound
        (hsplitCore_nonneg n hn)
        (hsplitCore n hn))
    hleftMul
    hrightMul
    hlogWidthMul
    hstackMul
end PebblingLean.Hypercube.PaperParameters
