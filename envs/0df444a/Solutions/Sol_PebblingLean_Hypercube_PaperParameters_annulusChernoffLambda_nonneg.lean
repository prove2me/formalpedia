-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.annulusChernoffLambda_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:56:57.135798+00:00
-- url     : https://prove2.me/submissions/ff470dfe-269b-460e-b5be-6ec0be924d6a

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
theorem _root_.solution (A K : ℝ) (n : ℕ) :
    0 ≤ annulusChernoffLambda A K n := by
  unfold annulusChernoffLambda
  positivity
end PebblingLean.Hypercube.PaperParameters
