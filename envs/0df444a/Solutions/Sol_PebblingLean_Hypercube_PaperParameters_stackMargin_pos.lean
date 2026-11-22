-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.stackMargin_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:58:56.187556+00:00
-- url     : https://prove2.me/submissions/fab9ee1f-5e06-44ba-a19e-d54a56a42f1e

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
theorem _root_.solution : 0 < stackMargin := by
  have hlogpos : 0 < Real.log ((32 : ℝ) / 27) :=
    Real.log_pos (by norm_num : (1 : ℝ) < (32 : ℝ) / 27)
  have htriple : 3 * stackMargin = Real.log ((32 : ℝ) / 27) := by
    rw [stackMargin]
    rw [show (32 : ℝ) / 27 = ((4 : ℝ) / 3) ^ 3 / 2 by norm_num]
    rw [Real.log_div
      (by norm_num : (((4 : ℝ) / 3) ^ 3) ≠ 0)
      (by norm_num : (2 : ℝ) ≠ 0)]
    rw [Real.log_pow]
    ring_nf
  nlinarith
end PebblingLean.Hypercube.PaperParameters
