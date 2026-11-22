-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.sqrt_three_n_log_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:56:37.198631+00:00
-- url     : https://prove2.me/submissions/55a93e6e-39d6-451c-8f0b-afa8a176434c

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
theorem _root_.solution (n : ℕ) :
    Real.sqrt (3 * (n : ℝ) * Real.log (n : ℝ)) =
      Real.sqrt 3 * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by
  rw [show 3 * (n : ℝ) * Real.log (n : ℝ) =
      3 * ((n : ℝ) * Real.log (n : ℝ)) by ring]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
end PebblingLean.Hypercube.PaperParameters
