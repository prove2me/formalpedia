-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.stack_core_log_budget_of_linear_margin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:11:31.955801+00:00
-- url     : https://prove2.me/submissions/14cb9c54-c222-4054-8679-50bd68423fcf

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_splitM_div_five_real_lower_bound
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_nat_div_real_le_div
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_annulusWidthCore_le_sqrt_three_n_log
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_stack_linear_margin_nonneg

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
          (A * Real.sqrt (3 * (n : ℝ) * Real.log (n : ℝ)) + 1) *
            Real.log 2 ≤
        (K * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) / 5 - 1) *
            Real.log 2 +
          ((3 : ℝ) * (n : ℝ) / 4) *
            (Real.log ((4 : ℝ) / 3) - Real.log 2 / 3)) :
    Real.log 2 + 2 * Real.log (n : ℝ) +
        (((splitA K n / 3 : ℕ) : ℝ) + annulusWidthCore A K n + 1) *
          Real.log 2 ≤
      ((splitM K n / 5 : ℕ) : ℝ) * Real.log 2 +
        (splitA K n : ℝ) * Real.log ((4 : ℝ) / 3) := by
  have hlog2_nonneg : 0 ≤ Real.log 2 :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hdiva := nat_div_real_le_div (splitA K n) 3 (by decide)
  have hwidth := annulusWidthCore_le_sqrt_three_n_log (K := K) hA hn
  have hlhs := mul_le_mul_of_nonneg_right
    (add_le_add_right (add_le_add hdiva hwidth) 1) hlog2_nonneg
  have hcore := mul_le_mul_of_nonneg_right
    (splitM_div_five_real_lower_bound (K := K) (n := n)) hlog2_nonneg
  have hmargin := mul_le_mul_of_nonneg_right ha_lower stack_linear_margin_nonneg
  linarith only [hlhs, hcore, hmargin, hcoarse]
end PebblingLean.Hypercube.PaperParameters
