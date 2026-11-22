-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.width_sqrt_margin_of_K_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:09:36.338381+00:00
-- url     : https://prove2.me/submissions/7e15fa75-a0fa-4805-8f1d-453563a2d178

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
theorem _root_.solution {A K : ℝ} {n : ℕ}
    (hKdom : 15 * A * Real.sqrt 3 ≤ K)
    (hbudget :
      Real.log 128 + 3 * Real.log 2 +
          Real.log ((((n + 1 : ℕ) : ℝ) * Real.log 2)) +
          4 * Real.log (n : ℝ) ≤
        (K / 15 * Real.log 2) *
          Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) :
    Real.log 128 + 3 * Real.log 2 +
        Real.log ((((n + 1 : ℕ) : ℝ) * Real.log 2)) +
        4 * Real.log (n : ℝ) ≤
      ((K / 5 - 2 * A * Real.sqrt 3) * Real.log 2) *
        Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by
  have hlog2_nonneg : 0 ≤ Real.log 2 :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hsqrt_nonneg :
      0 ≤ Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) :=
    Real.sqrt_nonneg _
  have hcoeff : K / 15 ≤ K / 5 - 2 * A * Real.sqrt 3 := by
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hcoeff hlog2_nonneg
  have hmul2 := mul_le_mul_of_nonneg_right hmul hsqrt_nonneg
  exact hbudget.trans hmul2
end PebblingLean.Hypercube.PaperParameters
