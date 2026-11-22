-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.explicitCutoff_splitThreshold
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:13:08.298193+00:00
-- url     : https://prove2.me/submissions/a57ff4fa-ad5c-49a1-a765-eee78d6c9e6e

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
theorem _root_.solution :
    (128 * (217 : ℝ) ^ 2) ^ 2 ≤ (explicitCutoff : ℝ) := by
  norm_num [explicitCutoff]
end PebblingLean.Hypercube.PaperParameters
