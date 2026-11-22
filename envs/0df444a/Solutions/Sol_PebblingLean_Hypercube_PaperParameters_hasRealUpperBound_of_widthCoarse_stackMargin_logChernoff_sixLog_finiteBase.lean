-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_widthCoarse_stackMargin_logChernoff_sixLog_finiteBase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:53:50.274498+00:00
-- url     : https://prove2.me/submissions/f89573cc-ca50-4404-9197-a6f36d758f02

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
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_stack_core_log_budget_of_linear_margin
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_tail_budget_of_six_log
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_leftChernoffTerm_le_exp_of_log_le
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_rightChernoffTerm_le_exp_of_log_le
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
    (hwidthCoarse :
      ∀ n : ℕ, n0 ≤ n →
        Real.log 128 + (2 *
            (A * Real.sqrt (3 * (n : ℝ) * Real.log (n : ℝ)) + 1)) *
            Real.log 2 +
            Real.log ((((n + 1 : ℕ) : ℝ) * Real.log 2)) ≤
          -4 * Real.log (n : ℝ) +
            (K * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) / 5 - 1) *
              Real.log 2)
    (hstackMargin :
      ∀ n : ℕ, n0 ≤ n →
        Real.log 2 + 2 * Real.log (n : ℝ) +
            (A * Real.sqrt (3 * (n : ℝ) * Real.log (n : ℝ)) + 1) *
              Real.log 2 ≤
          (K * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) / 5 - 1) *
              Real.log 2 +
            ((3 : ℝ) * (n : ℝ) / 4) *
              (Real.log ((4 : ℝ) / 3) - Real.log 2 / 3)) :
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
    (fun n hn =>
      tail_budget_of_six_log
        (by omega : 2 ≤ n)
        (htailSix n hn))
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
      stack_core_log_budget_of_linear_margin
        (A := A) (K := K) (n := n)
        hA
        (by omega : 2 ≤ n)
        (three_quarters_le_splitA_of_four_mul_le hquarter)
        (hstackMargin n hn))
end PebblingLean.Hypercube.PaperParameters
