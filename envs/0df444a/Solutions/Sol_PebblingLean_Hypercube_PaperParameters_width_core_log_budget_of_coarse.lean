-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.width_core_log_budget_of_coarse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:11:17.061935+00:00
-- url     : https://prove2.me/submissions/9fdc2e97-250e-4bf5-830c-3568b6c42051

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_splitM_div_five_real_lower_bound
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_annulusWidthCore_le_sqrt_three_n_log
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_log_splitA_succ_mul_log_two_le_log_n_succ_mul_log_two

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters
namespace PebblingLean.Hypercube.PaperParameters
theorem _root_.solution {A K : ℝ} {n : ℕ}
    (hA : 0 ≤ A) (hn : 2 ≤ n)
    (hcoarse :
      Real.log 128 + (2 *
          (A * Real.sqrt (3 * (n : ℝ) * Real.log (n : ℝ)) + 1)) *
          Real.log 2 +
          Real.log ((((n + 1 : ℕ) : ℝ) * Real.log 2)) ≤
        -4 * Real.log (n : ℝ) +
          (K * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) / 5 - 1) *
            Real.log 2) :
    Real.log 128 + (2 * (annulusWidthCore A K n + 1)) * Real.log 2 +
        Real.log ((((splitA K n + 1 : ℕ) : ℝ) * Real.log 2)) ≤
      -4 * Real.log (n : ℝ) +
        ((splitM K n / 5 : ℕ) : ℝ) * Real.log 2 := by
  have hlog2_nonneg : 0 ≤ Real.log 2 :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hwidth :=
    annulusWidthCore_le_sqrt_three_n_log
      (A := A) (K := K) (n := n) hA hn
  have hwidthTerm :
      (2 * (annulusWidthCore A K n + 1)) * Real.log 2 ≤
        (2 * (A * Real.sqrt (3 * (n : ℝ) * Real.log (n : ℝ)) + 1)) *
          Real.log 2 := by
    have hinside :
        2 * (annulusWidthCore A K n + 1) ≤
          2 * (A * Real.sqrt (3 * (n : ℝ) * Real.log (n : ℝ)) + 1) := by
      linarith
    exact mul_le_mul_of_nonneg_right hinside hlog2_nonneg
  have hlogTerm :=
    log_splitA_succ_mul_log_two_le_log_n_succ_mul_log_two
      (K := K) (n := n)
  have hcore := splitM_div_five_real_lower_bound (K := K) (n := n)
  have hrhs :
      -4 * Real.log (n : ℝ) +
          (K * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) / 5 - 1) *
            Real.log 2 ≤
        -4 * Real.log (n : ℝ) +
          ((splitM K n / 5 : ℕ) : ℝ) * Real.log 2 := by
    have hmul := mul_le_mul_of_nonneg_right hcore hlog2_nonneg
    linarith
  linarith
end PebblingLean.Hypercube.PaperParameters
