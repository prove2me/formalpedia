-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.annulusWidth_real_ge_of_core_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:06:41.709932+00:00
-- url     : https://prove2.me/submissions/42307ffb-8f32-4eed-9a5b-148f9e18b2d7

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_annulusWidthCore_le_width_real

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters
namespace PebblingLean.Hypercube.PaperParameters
theorem _root_.solution {A K : ℝ} {n : ℕ}
    (hcore : 9 ≤ annulusWidthCore A K n) :
    9 ≤ (annulusWidth A K n : ℝ) :=
  hcore.trans annulusWidthCore_le_width_real
end PebblingLean.Hypercube.PaperParameters
