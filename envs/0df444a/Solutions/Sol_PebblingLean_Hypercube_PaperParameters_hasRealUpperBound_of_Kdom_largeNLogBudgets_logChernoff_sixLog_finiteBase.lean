-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_Kdom_largeNLogBudgets_logChernoff_sixLog_finiteBase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:56:56.190971+00:00
-- url     : https://prove2.me/submissions/60147aea-fb26-4f72-9ee4-2d0a70527a55

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_width_log_budget_of_simplified_log_budget
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_width_simple_budget_of_const_budget
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_stack_linear_budget_of_sqrt_and_const_bounds
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_hasRealUpperBound_of_Kdom_logBudgets_logChernoff_sixLog_finiteBase

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
    (hA : 0 ≤ A)
    (hKdom : 15 * A * Real.sqrt 3 ≤ K)
    (hKlarge : 150 ≤ K * Real.log 2)
    (hsplitLogLinear :
      ∀ n : ℕ, n0 ≤ n →
        K ^ 2 * Real.log (n : ℝ) ≤ (n : ℝ) / 64)
    (hleftLog :
      ∀ n : ℕ, n0 ≤ n →
        annulusChernoffLambda A K n * (rIn A K n : ℝ) +
            (splitA K n : ℝ) *
              Real.log (((1 : ℝ) / 3) *
                  Real.exp (-(annulusChernoffLambda A K n)) +
                ((2 : ℝ) / 3)) ≤ -(tailExponent n))
    (hrightLog :
      ∀ n : ℕ, n0 ≤ n →
        -(annulusChernoffLambda A K n * (rOut A K n : ℝ)) +
            (splitA K n : ℝ) *
              Real.log (((1 : ℝ) / 3) *
                  Real.exp (annulusChernoffLambda A K n) +
                ((2 : ℝ) / 3)) ≤ -(tailExponent n))
    (htailSix :
      ∀ n : ℕ, n0 ≤ n →
        6 * Real.log (n : ℝ) ≤ tailExponent n)
    (hwidthConst :
      ∀ n : ℕ, n0 ≤ n →
        Real.log 128 + 4 * Real.log 2 ≤
          (K / 30 * Real.log 2) *
            Real.sqrt ((n : ℝ) * Real.log (n : ℝ)))
    (hstackSqrt :
      ∀ n : ℕ, n0 ≤ n →
        4 * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤
          (n : ℝ) *
            (Real.log ((4 : ℝ) / 3) - Real.log 2 / 3))
    (hstackConst :
      ∀ n : ℕ, n0 ≤ n →
        12 * Real.log 2 ≤
          (n : ℝ) *
            (Real.log ((4 : ℝ) / 3) - Real.log 2 / 3)) :
    HasRealHypercubePebblingUpperBound
      (Real.exp (4 * loss n0) *
        finiteBaseNormalizedBound (recursiveCostBound K n0) n0) :=
  hasRealUpperBound_of_Kdom_logBudgets_logChernoff_sixLog_finiteBase
    (K := K) (A := A) (n0 := n0) (tailExponent := tailExponent)
    hn0_pos
    hn0_growth
    hK
    hA
    hKdom
    hsplitLogLinear
    hleftLog
    hrightLog
    htailSix
    (fun n hn =>
      width_log_budget_of_simplified_log_budget
        (by omega : 1 ≤ n)
        (width_simple_budget_of_const_budget
          (by omega : 1 ≤ n)
          hKlarge
          (hwidthConst n hn)))
    (fun n hn =>
      stack_linear_budget_of_sqrt_and_const_bounds
        (by omega : 1 ≤ n)
        (hstackSqrt n hn)
        (hstackConst n hn))
end PebblingLean.Hypercube.PaperParameters
