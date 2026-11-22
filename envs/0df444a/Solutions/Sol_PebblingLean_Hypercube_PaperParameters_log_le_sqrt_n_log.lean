-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.log_le_sqrt_n_log
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:59:45.818804+00:00
-- url     : https://prove2.me/submissions/523f0512-b0d6-4126-b979-16b7c366e976

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters
namespace PebblingLean.Hypercube.PaperParameters
theorem _root_.solution {n : ℕ} (hn : 1 ≤ n) :
    Real.log (n : ℝ) ≤
      Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by
  have hlog_nonneg : 0 ≤ Real.log (n : ℝ) :=
    Real.log_natCast_nonneg n
  have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
  have hlog_le_n : Real.log (n : ℝ) ≤ (n : ℝ) :=
    Real.log_le_self hn_nonneg
  have hsq :
      (Real.log (n : ℝ)) ^ 2 ≤
        (n : ℝ) * Real.log (n : ℝ) := by
    calc
      (Real.log (n : ℝ)) ^ 2
          = Real.log (n : ℝ) * Real.log (n : ℝ) := by ring
      _ ≤ (n : ℝ) * Real.log (n : ℝ) :=
          mul_le_mul_of_nonneg_right hlog_le_n hlog_nonneg
  have hsqrt := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq_eq_abs, abs_of_nonneg hlog_nonneg] at hsqrt
end PebblingLean.Hypercube.PaperParameters
