-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_coarseLogThresholds_Knonneg_standardLambda_logChernoff_finiteBase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:54:55.12951+00:00
-- url     : https://prove2.me/submissions/1ca2fae6-976d-4544-811e-611ce7b634a3

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_leftChernoffTerm_le_exp_of_log_le
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_rightChernoffTerm_le_exp_of_log_le
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_hasRealUpperBound_of_coarseLogThresholds_Knonneg_standardLambda_tailExponent_finiteBase

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
    (htailBudget :
      ∀ n : ℕ, n0 ≤ n →
        Real.log 16 + 2 * Real.log (n : ℝ) ≤ tailExponent n)
    (hwidthCoarse :
      ∀ n : ℕ, n0 ≤ n →
        Real.log 128 + (2 *
            (A * Real.sqrt (3 * (n : ℝ) * Real.log (n : ℝ)) + 1)) *
            Real.log 2 +
            Real.log ((((n + 1 : ℕ) : ℝ) * Real.log 2)) ≤
          -4 * Real.log (n : ℝ) +
            (K * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) / 5 - 1) *
              Real.log 2)
    (hstackCoarse :
      ∀ n : ℕ, n0 ≤ n →
        Real.log 2 + 2 * Real.log (n : ℝ) +
            ((n : ℝ) / 3 +
                A * Real.sqrt (3 * (n : ℝ) * Real.log (n : ℝ)) + 1) *
              Real.log 2 ≤
          (K * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) / 5 - 1) *
              Real.log 2 +
            ((3 : ℝ) * (n : ℝ) / 4) * Real.log ((4 : ℝ) / 3)) :
    HasRealHypercubePebblingUpperBound
      (Real.exp (4 * loss n0) *
        finiteBaseNormalizedBound (recursiveCostBound K n0) n0) :=
  hasRealUpperBound_of_coarseLogThresholds_Knonneg_standardLambda_tailExponent_finiteBase
    (K := K) (A := A) (n0 := n0) (tailExponent := tailExponent)
    hn0_pos
    hn0_growth
    hK
    hA
    hsplitLogLinear
    (fun n hn =>
      leftChernoffTerm_le_exp_of_log_le
        (A := A) (K := K) (lam := annulusChernoffLambda A K)
        (n := n) (E := tailExponent n)
        (hleftLog n hn))
    (fun n hn =>
      rightChernoffTerm_le_exp_of_log_le
        (A := A) (K := K) (lam := annulusChernoffLambda A K)
        (n := n) (E := tailExponent n)
        (hrightLog n hn))
    htailBudget
    hwidthCoarse
    hstackCoarse
end PebblingLean.Hypercube.PaperParameters
