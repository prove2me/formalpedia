-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_Kdom_logBudgets_logChernoff_sixLog_finiteBase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:55:50.158157+00:00
-- url     : https://prove2.me/submissions/aea7e3ed-03c9-45be-933d-a489ecd539d1

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_width_sqrt_margin_of_K_ge
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_stack_sqrt_margin_of_linear_budget
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_hasRealUpperBound_of_sqrtMargins_logChernoff_sixLog_finiteBase

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
    (hwidthBudget :
      ∀ n : ℕ, n0 ≤ n →
        Real.log 128 + 3 * Real.log 2 +
            Real.log ((((n + 1 : ℕ) : ℝ) * Real.log 2)) +
            4 * Real.log (n : ℝ) ≤
          (K / 15 * Real.log 2) *
            Real.sqrt ((n : ℝ) * Real.log (n : ℝ)))
    (hstackBudget :
      ∀ n : ℕ, n0 ≤ n →
        2 * Real.log (n : ℝ) + 3 * Real.log 2 ≤
          ((3 : ℝ) * (n : ℝ) / 4) *
            (Real.log ((4 : ℝ) / 3) - Real.log 2 / 3)) :
    HasRealHypercubePebblingUpperBound
      (Real.exp (4 * loss n0) *
        finiteBaseNormalizedBound (recursiveCostBound K n0) n0) :=
  hasRealUpperBound_of_sqrtMargins_logChernoff_sixLog_finiteBase
    (K := K) (A := A) (n0 := n0) (tailExponent := tailExponent)
    hn0_pos
    hn0_growth
    hK
    hA
    hsplitLogLinear
    hleftLog
    hrightLog
    htailSix
    (fun n hn => width_sqrt_margin_of_K_ge hKdom (hwidthBudget n hn))
    (fun n hn =>
      stack_sqrt_margin_of_linear_budget
        (by nlinarith : 5 * A * Real.sqrt 3 ≤ K)
        (hstackBudget n hn))
end PebblingLean.Hypercube.PaperParameters
