-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.annulusWidthCore_le_width_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:57:35.582121+00:00
-- url     : https://prove2.me/submissions/d1b2d3a8-0086-4afd-a69c-91085cd26aaf

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
    annulusWidthCore A K n ≤ (annulusWidth A K n : ℝ) := by
  unfold annulusWidth annulusWidthCore
  exact Nat.le_ceil
    (A * Real.sqrt ((splitA K n : ℝ) * Real.log (2 * (n : ℝ) ^ 2)))
end PebblingLean.Hypercube.PaperParameters
