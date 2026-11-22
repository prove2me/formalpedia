-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.explicitCutoff_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:03:11.012166+00:00
-- url     : https://prove2.me/submissions/e75738c3-1a8a-4c22-b43c-1e0931cec198

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
theorem _root_.solution : 0 < explicitCutoff := by
  norm_num [explicitCutoff]
end PebblingLean.Hypercube.PaperParameters
