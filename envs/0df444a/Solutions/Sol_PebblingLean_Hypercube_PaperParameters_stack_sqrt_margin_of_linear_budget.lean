-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.stack_sqrt_margin_of_linear_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:09:43.596671+00:00
-- url     : https://prove2.me/submissions/58ddaa1a-a90d-43d8-9c5c-acf7d9691031

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
    (hKdom : 5 * A * Real.sqrt 3 ≤ K)
    (hbudget :
      2 * Real.log (n : ℝ) + 3 * Real.log 2 ≤
        ((3 : ℝ) * (n : ℝ) / 4) *
          (Real.log ((4 : ℝ) / 3) - Real.log 2 / 3)) :
    2 * Real.log (n : ℝ) + 3 * Real.log 2 ≤
      ((K / 5 - A * Real.sqrt 3) * Real.log 2) *
          Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) +
        ((3 : ℝ) * (n : ℝ) / 4) *
          (Real.log ((4 : ℝ) / 3) - Real.log 2 / 3) := by
  have hlog2_nonneg : 0 ≤ Real.log 2 :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hsqrt_nonneg :
      0 ≤ Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) :=
    Real.sqrt_nonneg _
  have hcoeff : 0 ≤ K / 5 - A * Real.sqrt 3 := by nlinarith
  have hterm :
      0 ≤ ((K / 5 - A * Real.sqrt 3) * Real.log 2) *
        Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by
    positivity
  linarith
end PebblingLean.Hypercube.PaperParameters
