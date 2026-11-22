-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.width_simple_budget_of_const_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:10:22.297843+00:00
-- url     : https://prove2.me/submissions/f3e037ae-1426-4c60-aeac-4e0df94f4d09

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_log_le_sqrt_n_log

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters
namespace PebblingLean.Hypercube.PaperParameters
theorem _root_.solution {K : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (hKlarge : 150 ≤ K * Real.log 2)
    (hconst :
      Real.log 128 + 4 * Real.log 2 ≤
        (K / 30 * Real.log 2) *
          Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) :
    Real.log 128 + 4 * Real.log 2 + 5 * Real.log (n : ℝ) ≤
      (K / 15 * Real.log 2) *
        Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by
  have hsqrt_nonneg :
      0 ≤ Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) :=
    Real.sqrt_nonneg _
  have hlog_sqrt := log_le_sqrt_n_log (n := n) hn
  have hcoeff : (5 : ℝ) ≤ K / 30 * Real.log 2 := by
    nlinarith
  have hlog_part :
      5 * Real.log (n : ℝ) ≤
        (K / 30 * Real.log 2) *
          Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by
    have hlog_le_sqrt_scaled :
        5 * Real.log (n : ℝ) ≤
          5 * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog_sqrt (by norm_num : (0 : ℝ) ≤ 5)
    have hsqrt_scaled_le_budget :
        5 * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤
          (K / 30 * Real.log 2) *
            Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) :=
      mul_le_mul_of_nonneg_right hcoeff hsqrt_nonneg
    exact hlog_le_sqrt_scaled.trans hsqrt_scaled_le_budget
  nlinarith
end PebblingLean.Hypercube.PaperParameters
