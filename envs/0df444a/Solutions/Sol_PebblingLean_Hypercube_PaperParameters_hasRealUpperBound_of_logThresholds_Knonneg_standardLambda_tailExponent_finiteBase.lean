-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_logThresholds_Knonneg_standardLambda_tailExponent_finiteBase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:51:57.905228+00:00
-- url     : https://prove2.me/submissions/0996f37c-79d9-4e19-95cb-f685d64f9f51

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_bernstein_width_mul_le_of_log_budget
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_hasRealUpperBound_of_logLinearSplit_Knonneg_standardLambda_tailExponent_stackLog_finiteBase

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters
namespace PebblingLean.Hypercube.PaperParameters
theorem _root_.solution
    {K A : ℝ} {n0 : ℕ} {tailExponent : ℕ → ℝ}
    (hn0_pos : 0 < n0)
    (hn0_growth : 58 ≤ n0)
    (hK : 0 ≤ K)
    (hsplitLogLinear :
      ∀ n : ℕ, n0 ≤ n →
        K ^ 2 * Real.log (n : ℝ) ≤ (n : ℝ) / 64)
    (hleftExp :
      ∀ n : ℕ, n0 ≤ n →
        leftChernoffTerm A K (annulusChernoffLambda A K) n ≤
          Real.exp (-(tailExponent n)))
    (hrightExp :
      ∀ n : ℕ, n0 ≤ n →
        rightChernoffTerm A K (annulusChernoffLambda A K) n ≤
          Real.exp (-(tailExponent n)))
    (htailBudget :
      ∀ n : ℕ, n0 ≤ n →
        Real.log 16 + 2 * Real.log (n : ℝ) ≤ tailExponent n)
    (hwidthLog :
      ∀ n : ℕ, n0 ≤ n →
        Real.log 128 + ((2 * annulusWidth A K n : ℕ) : ℝ) * Real.log 2 +
            Real.log ((((splitA K n + 1 : ℕ) : ℝ) * Real.log 2)) ≤
          -4 * Real.log (n : ℝ) +
            ((splitM K n / 5 : ℕ) : ℝ) * Real.log 2)
    (hstackLog :
      ∀ n : ℕ, n0 ≤ n →
        Real.log 2 + 2 * Real.log (n : ℝ) +
            (rOut A K n : ℝ) * Real.log 2 ≤
          ((splitM K n / 5 : ℕ) : ℝ) * Real.log 2 +
            (splitA K n : ℝ) * Real.log ((4 : ℝ) / 3)) :
    HasRealHypercubePebblingUpperBound
      (Real.exp (4 * loss n0) *
        finiteBaseNormalizedBound (recursiveCostBound K n0) n0) :=
  hasRealUpperBound_of_logLinearSplit_Knonneg_standardLambda_tailExponent_stackLog_finiteBase
    (K := K) (A := A) (n0 := n0) (tailExponent := tailExponent)
    hn0_pos
    hn0_growth
    hK
    hsplitLogLinear
    hleftExp
    hrightExp
    htailBudget
    (fun n hn =>
      bernstein_width_mul_le_of_log_budget
        (lt_of_lt_of_le hn0_pos hn)
        (hwidthLog n hn))
    hstackLog
end PebblingLean.Hypercube.PaperParameters
