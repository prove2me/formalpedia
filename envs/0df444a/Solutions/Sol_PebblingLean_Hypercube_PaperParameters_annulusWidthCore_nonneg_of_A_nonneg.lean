-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.annulusWidthCore_nonneg_of_A_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:55:41.41142+00:00
-- url     : https://prove2.me/submissions/eee86c2d-1446-4731-8de9-9998019deee4

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
    (hA : 0 ≤ A) :
    0 ≤ annulusWidthCore A K n := by
  unfold annulusWidthCore
  positivity
end PebblingLean.Hypercube.PaperParameters
