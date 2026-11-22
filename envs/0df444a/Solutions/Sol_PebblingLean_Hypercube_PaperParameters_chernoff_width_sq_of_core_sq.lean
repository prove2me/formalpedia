-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.chernoff_width_sq_of_core_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:07:29.507011+00:00
-- url     : https://prove2.me/submissions/7c216320-d016-409f-b26c-0339f2c10f7d

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_annulusWidthCore_sq_le_width_sq_of_A_nonneg

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters
namespace PebblingLean.Hypercube.PaperParameters
theorem _root_.solution {A K : ℝ} {n : ℕ}
    (hA : 0 ≤ A)
    (hcoreSq :
      12 * ((splitA K n : ℝ) + 1) * Real.log (n : ℝ) ≤
        (annulusWidthCore A K n) ^ 2) :
    12 * ((splitA K n : ℝ) + 1) * Real.log (n : ℝ) ≤
      (annulusWidth A K n : ℝ) ^ 2 :=
  hcoreSq.trans (annulusWidthCore_sq_le_width_sq_of_A_nonneg
    (A := A) (K := K) (n := n) hA)
end PebblingLean.Hypercube.PaperParameters
