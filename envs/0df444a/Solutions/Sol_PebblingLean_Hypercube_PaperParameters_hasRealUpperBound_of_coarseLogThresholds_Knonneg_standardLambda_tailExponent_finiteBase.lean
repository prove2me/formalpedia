-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_coarseLogThresholds_Knonneg_standardLambda_tailExponent_finiteBase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:53:49.587745+00:00
-- url     : https://prove2.me/submissions/30d43374-0dcb-454a-abcd-2d16b6ddd2aa

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_three_quarters_le_splitA_of_four_mul_le
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_four_mul_splitM_le_of_real_le_quarter
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_splitM_real_le_quarter_of_ceiling_bound
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_splitM_core_nonneg_of_K_nonneg
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_split_core_bound_of_log_le_linear
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_width_core_log_budget_of_coarse
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_stack_core_log_budget_of_coarse
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_hasRealUpperBound_of_coreLogThresholds_Knonneg_standardLambda_tailExponent_finiteBase

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
  hasRealUpperBound_of_coreLogThresholds_Knonneg_standardLambda_tailExponent_finiteBase
    (K := K) (A := A) (n0 := n0) (tailExponent := tailExponent)
    hn0_pos
    hn0_growth
    hK
    hA
    hsplitLogLinear
    hleftExp
    hrightExp
    htailBudget
    (fun n hn =>
      width_core_log_budget_of_coarse
        (A := A) (K := K) (n := n)
        hA
        (by omega : 2 ≤ n)
        (hwidthCoarse n hn))
    (fun n hn =>
      let hsplitCore :=
        split_core_bound_of_log_le_linear
          (K := K) (n := n)
          hK
          (by omega : 8 ≤ n)
          (hsplitLogLinear n hn)
      let hquarter :=
        four_mul_splitM_le_of_real_le_quarter
          (splitM_real_le_quarter_of_ceiling_bound
            (splitM_core_nonneg_of_K_nonneg hK)
            hsplitCore)
      stack_core_log_budget_of_coarse
        (A := A) (K := K) (n := n)
        hA
        (by omega : 2 ≤ n)
        (three_quarters_le_splitA_of_four_mul_le hquarter)
        (hstackCoarse n hn))
end PebblingLean.Hypercube.PaperParameters
