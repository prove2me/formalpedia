-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.splitM_core_nonneg_of_K_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:56:04.190751+00:00
-- url     : https://prove2.me/submissions/1272eb1a-93e7-4171-b976-9d4f2a90b1f2

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
theorem _root_.solution {K : ℝ} {n : ℕ}
    (hK : 0 ≤ K) :
    0 ≤ K * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) :=
  mul_nonneg hK (Real.sqrt_nonneg _)
end PebblingLean.Hypercube.PaperParameters
