-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_sqrtMargins_logChernoff_sixLog_finiteBase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:54:55.57243+00:00
-- url     : https://prove2.me/submissions/c0a371be-ed78-4f1d-ad69-32f2d92670ec

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_width_coarse_of_sqrt_margin
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_stack_margin_of_sqrt_margin
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_hasRealUpperBound_of_widthCoarse_stackMargin_logChernoff_sixLog_finiteBase

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
    (hwidthSqrt :
      ∀ n : ℕ, n0 ≤ n →
        Real.log 128 + 3 * Real.log 2 +
            Real.log ((((n + 1 : ℕ) : ℝ) * Real.log 2)) +
            4 * Real.log (n : ℝ) ≤
          ((K / 5 - 2 * A * Real.sqrt 3) * Real.log 2) *
            Real.sqrt ((n : ℝ) * Real.log (n : ℝ)))
    (hstackSqrt :
      ∀ n : ℕ, n0 ≤ n →
        2 * Real.log (n : ℝ) + 3 * Real.log 2 ≤
          ((K / 5 - A * Real.sqrt 3) * Real.log 2) *
              Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) +
            ((3 : ℝ) * (n : ℝ) / 4) *
              (Real.log ((4 : ℝ) / 3) - Real.log 2 / 3)) :
    HasRealHypercubePebblingUpperBound
      (Real.exp (4 * loss n0) *
        finiteBaseNormalizedBound (recursiveCostBound K n0) n0) :=
  hasRealUpperBound_of_widthCoarse_stackMargin_logChernoff_sixLog_finiteBase
    (K := K) (A := A) (n0 := n0) (tailExponent := tailExponent)
    hn0_pos
    hn0_growth
    hK
    hA
    hsplitLogLinear
    hleftLog
    hrightLog
    htailSix
    (fun n hn => width_coarse_of_sqrt_margin (hwidthSqrt n hn))
    (fun n hn => stack_margin_of_sqrt_margin (hstackSqrt n hn))
end PebblingLean.Hypercube.PaperParameters
