-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.rIn_le_rOut
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:06:34.79656+00:00
-- url     : https://prove2.me/submissions/b1609896-0354-4249-9979-3d90cdece61f

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
theorem _root_.solution {A K : ℝ} {n : ℕ} :
    rIn A K n ≤ rOut A K n := by
  unfold rIn rOut
  omega
end PebblingLean.Hypercube.PaperParameters
