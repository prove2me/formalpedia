-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.stack_log_budget_of_core_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:11:39.084129+00:00
-- url     : https://prove2.me/submissions/d69e011b-4093-496a-9ba2-bc60a73a82ee

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_rOut_real_le_div_three_add_widthCore_add_one_of_A_nonneg

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters
namespace PebblingLean.Hypercube.PaperParameters
theorem _root_.solution {A K : ℝ} {n : ℕ}
    (hA : 0 ≤ A)
    (hcoreBudget :
      Real.log 2 + 2 * Real.log (n : ℝ) +
          (((splitA K n / 3 : ℕ) : ℝ) + annulusWidthCore A K n + 1) *
            Real.log 2 ≤
        ((splitM K n / 5 : ℕ) : ℝ) * Real.log 2 +
          (splitA K n : ℝ) * Real.log ((4 : ℝ) / 3)) :
    Real.log 2 + 2 * Real.log (n : ℝ) +
        (rOut A K n : ℝ) * Real.log 2 ≤
      ((splitM K n / 5 : ℕ) : ℝ) * Real.log 2 +
        (splitA K n : ℝ) * Real.log ((4 : ℝ) / 3) := by
  have hlog2_nonneg : 0 ≤ Real.log 2 :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hrOut :=
    rOut_real_le_div_three_add_widthCore_add_one_of_A_nonneg
      (A := A) (K := K) (n := n) hA
  have hrOutLog :
      (rOut A K n : ℝ) * Real.log 2 ≤
        (((splitA K n / 3 : ℕ) : ℝ) + annulusWidthCore A K n + 1) *
          Real.log 2 :=
    mul_le_mul_of_nonneg_right hrOut hlog2_nonneg
  linarith
end PebblingLean.Hypercube.PaperParameters
