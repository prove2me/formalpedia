-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.stack_core_log_budget_of_coarse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:11:21.851255+00:00
-- url     : https://prove2.me/submissions/94b42de2-2e88-47b4-ad71-9e3dd1b4c852

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_splitM_div_five_real_lower_bound
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_splitA_div_three_real_le_n_div_three
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_annulusWidthCore_le_sqrt_three_n_log

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters
namespace PebblingLean.Hypercube.PaperParameters
theorem _root_.solution {A K : ℝ} {n : ℕ}
    (hA : 0 ≤ A) (hn : 2 ≤ n)
    (ha_lower : (3 : ℝ) * (n : ℝ) / 4 ≤ (splitA K n : ℝ))
    (hcoarse :
      Real.log 2 + 2 * Real.log (n : ℝ) +
          ((n : ℝ) / 3 +
              A * Real.sqrt (3 * (n : ℝ) * Real.log (n : ℝ)) + 1) *
            Real.log 2 ≤
        (K * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) / 5 - 1) *
            Real.log 2 +
          ((3 : ℝ) * (n : ℝ) / 4) * Real.log ((4 : ℝ) / 3)) :
    Real.log 2 + 2 * Real.log (n : ℝ) +
        (((splitA K n / 3 : ℕ) : ℝ) + annulusWidthCore A K n + 1) *
          Real.log 2 ≤
      ((splitM K n / 5 : ℕ) : ℝ) * Real.log 2 +
        (splitA K n : ℝ) * Real.log ((4 : ℝ) / 3) := by
  have hlog2_nonneg : 0 ≤ Real.log 2 :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hlog43_nonneg : 0 ≤ Real.log ((4 : ℝ) / 3) :=
    (Real.log_pos (by norm_num : (1 : ℝ) < ((4 : ℝ) / 3))).le
  have hdiv := splitA_div_three_real_le_n_div_three (K := K) (n := n)
  have hwidth :=
    annulusWidthCore_le_sqrt_three_n_log
      (A := A) (K := K) (n := n) hA hn
  have hlhsTerm :
      (((splitA K n / 3 : ℕ) : ℝ) + annulusWidthCore A K n + 1) *
          Real.log 2 ≤
        ((n : ℝ) / 3 +
            A * Real.sqrt (3 * (n : ℝ) * Real.log (n : ℝ)) + 1) *
          Real.log 2 := by
    have hinside :
        ((splitA K n / 3 : ℕ) : ℝ) + annulusWidthCore A K n + 1 ≤
          (n : ℝ) / 3 +
            A * Real.sqrt (3 * (n : ℝ) * Real.log (n : ℝ)) + 1 := by
      linarith
    exact mul_le_mul_of_nonneg_right hinside hlog2_nonneg
  have hcore := splitM_div_five_real_lower_bound (K := K) (n := n)
  have hrhs :
      (K * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) / 5 - 1) *
            Real.log 2 +
          ((3 : ℝ) * (n : ℝ) / 4) * Real.log ((4 : ℝ) / 3) ≤
        ((splitM K n / 5 : ℕ) : ℝ) * Real.log 2 +
          (splitA K n : ℝ) * Real.log ((4 : ℝ) / 3) := by
    have hcore_log2 := mul_le_mul_of_nonneg_right hcore hlog2_nonneg
    have hlower_log43 := mul_le_mul_of_nonneg_right ha_lower hlog43_nonneg
    linarith
  linarith
end PebblingLean.Hypercube.PaperParameters
