-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.annulusWidth_real_le_core_add_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:08:03.946692+00:00
-- url     : https://prove2.me/submissions/2ebbe1a3-c38b-4ef9-8854-aa12509ea904

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_annulusWidth_real_lt_core_add_one

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters
namespace PebblingLean.Hypercube.PaperParameters
theorem _root_.solution {A K : ℝ} {n : ℕ}
    (hcore : 0 ≤ annulusWidthCore A K n) :
    (annulusWidth A K n : ℝ) ≤ annulusWidthCore A K n + 1 :=
  le_of_lt (annulusWidth_real_lt_core_add_one hcore)
end PebblingLean.Hypercube.PaperParameters
