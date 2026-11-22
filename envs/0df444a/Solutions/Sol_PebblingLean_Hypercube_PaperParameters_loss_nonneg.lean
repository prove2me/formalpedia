-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.loss_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:55:36.393196+00:00
-- url     : https://prove2.me/submissions/3fa6e89c-29b5-4f79-886b-2840a9af8abe

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
theorem _root_.solution (n : ℕ) : 0 ≤ loss n := by
  unfold loss
  positivity
end PebblingLean.Hypercube.PaperParameters
