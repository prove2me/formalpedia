-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.stack_linear_budget_of_sqrt_and_const_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:10:36.379225+00:00
-- url     : https://prove2.me/submissions/015d0279-781e-4af1-af77-00b73b5c115e

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_stack_linear_budget_of_split_bounds
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_log_le_sqrt_n_log

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters
namespace PebblingLean.Hypercube.PaperParameters
theorem _root_.solution {n : ℕ}
    (hn : 1 ≤ n)
    (hsqrt :
      4 * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤
        (n : ℝ) *
          (Real.log ((4 : ℝ) / 3) - Real.log 2 / 3))
    (hconst :
      12 * Real.log 2 ≤
        (n : ℝ) *
          (Real.log ((4 : ℝ) / 3) - Real.log 2 / 3)) :
    2 * Real.log (n : ℝ) + 3 * Real.log 2 ≤
      ((3 : ℝ) * (n : ℝ) / 4) *
        (Real.log ((4 : ℝ) / 3) - Real.log 2 / 3) := by
  have hlog_sqrt := log_le_sqrt_n_log (n := n) hn
  have hlog_part :
      2 * Real.log (n : ℝ) ≤
        ((n : ℝ) / 2) *
          (Real.log ((4 : ℝ) / 3) - Real.log 2 / 3) := by
    have hlog_le_sqrt_scaled :
        2 * Real.log (n : ℝ) ≤
          2 * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hsqrt_scaled_le_margin :
        2 * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤
          ((n : ℝ) / 2) *
            (Real.log ((4 : ℝ) / 3) - Real.log 2 / 3) := by
      nlinarith
    exact hlog_le_sqrt_scaled.trans hsqrt_scaled_le_margin
  have hconst_part :
      3 * Real.log 2 ≤
        ((n : ℝ) / 4) *
          (Real.log ((4 : ℝ) / 3) - Real.log 2 / 3) := by
    nlinarith
  exact stack_linear_budget_of_split_bounds hlog_part hconst_part
end PebblingLean.Hypercube.PaperParameters
