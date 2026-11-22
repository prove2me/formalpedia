-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.annulusWidth_real_le_core_add_one_of_A_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:09:12.289749+00:00
-- url     : https://prove2.me/submissions/3e7f73a0-6920-431a-aaa0-9dda2b0a4fe1

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_annulusWidthCore_nonneg_of_A_nonneg
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_annulusWidth_real_le_core_add_one

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters
namespace PebblingLean.Hypercube.PaperParameters
theorem _root_.solution {A K : ℝ} {n : ℕ}
    (hA : 0 ≤ A) :
    (annulusWidth A K n : ℝ) ≤ annulusWidthCore A K n + 1 :=
  annulusWidth_real_le_core_add_one
    (annulusWidthCore_nonneg_of_A_nonneg hA)
end PebblingLean.Hypercube.PaperParameters
