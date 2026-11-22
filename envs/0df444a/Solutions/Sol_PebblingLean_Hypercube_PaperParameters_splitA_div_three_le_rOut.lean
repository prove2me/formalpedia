-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.splitA_div_three_le_rOut
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:06:35.225273+00:00
-- url     : https://prove2.me/submissions/32bc21b6-fcba-44b9-9d4c-c71dc875f219

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
    splitA K n / 3 ≤ rOut A K n := by
  unfold rOut
  omega
end PebblingLean.Hypercube.PaperParameters
