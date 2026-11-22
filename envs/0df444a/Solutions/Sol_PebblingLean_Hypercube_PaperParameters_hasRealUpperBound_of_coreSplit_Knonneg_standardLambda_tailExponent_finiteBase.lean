-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_coreSplit_Knonneg_standardLambda_tailExponent_finiteBase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:48:48.510855+00:00
-- url     : https://prove2.me/submissions/b1954032-abd1-465c-964d-4cbc40a9d3d8

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_sixteen_exp_neg_le_loss_of_log_budget
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_hasRealUpperBound_of_coreSplit_Knonneg_standardLambda_finiteBase

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
    (hsplitCore :
      ∀ n : ℕ, n0 ≤ n →
        K * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) + 1 ≤
          (n : ℝ) / 4)
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
  hasRealUpperBound_of_coreSplit_Knonneg_standardLambda_finiteBase
    (K := K) (A := A) (n0 := n0)
    hn0_pos
    hn0_growth
    hK
    hsplitCore
    (fun n hn => by
      have hbudget :=
        sixteen_exp_neg_le_loss_of_log_budget
          (lt_of_lt_of_le hn0_pos hn) (htailBudget n hn)
      have hmul := mul_le_mul_of_nonneg_left (hleftExp n hn) (by norm_num : (0 : ℝ) ≤ 16)
      exact hmul.trans hbudget)
    (fun n hn => by
      have hbudget :=
        sixteen_exp_neg_le_loss_of_log_budget
          (lt_of_lt_of_le hn0_pos hn) (htailBudget n hn)
      have hmul := mul_le_mul_of_nonneg_left (hrightExp n hn) (by norm_num : (0 : ℝ) ≤ 16)
      exact hmul.trans hbudget)
    hlogWidthMul
    hstackMul
end PebblingLean.Hypercube.PaperParameters
