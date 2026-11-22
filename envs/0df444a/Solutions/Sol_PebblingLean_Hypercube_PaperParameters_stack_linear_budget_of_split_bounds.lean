-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.stack_linear_budget_of_split_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:59:44.23465+00:00
-- url     : https://prove2.me/submissions/e57534a7-6468-4e8c-8a8e-a8df2455d13c

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
theorem _root_.solution {n : ℕ}
    (hlog :
      2 * Real.log (n : ℝ) ≤
        ((n : ℝ) / 2) *
          (Real.log ((4 : ℝ) / 3) - Real.log 2 / 3))
    (hconst :
      3 * Real.log 2 ≤
        ((n : ℝ) / 4) *
          (Real.log ((4 : ℝ) / 3) - Real.log 2 / 3)) :
    2 * Real.log (n : ℝ) + 3 * Real.log 2 ≤
      ((3 : ℝ) * (n : ℝ) / 4) *
        (Real.log ((4 : ℝ) / 3) - Real.log 2 / 3) := by
  nlinarith
end PebblingLean.Hypercube.PaperParameters
