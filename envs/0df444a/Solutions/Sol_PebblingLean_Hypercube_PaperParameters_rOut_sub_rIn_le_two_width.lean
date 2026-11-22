-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.rOut_sub_rIn_le_two_width
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:07:02.012685+00:00
-- url     : https://prove2.me/submissions/952313d2-5730-4142-9a99-1643f0acf63f

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
    rOut A K n - rIn A K n ≤ 2 * annulusWidth A K n := by
  unfold rOut rIn
  omega
end PebblingLean.Hypercube.PaperParameters
