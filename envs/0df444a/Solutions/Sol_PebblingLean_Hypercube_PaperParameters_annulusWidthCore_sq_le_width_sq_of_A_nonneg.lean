-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.annulusWidthCore_sq_le_width_sq_of_A_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:06:42.09264+00:00
-- url     : https://prove2.me/submissions/987f3d71-24b1-43e1-9f8c-879aaedb41c2

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_annulusWidthCore_nonneg_of_A_nonneg
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_annulusWidthCore_le_width_real

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters
namespace PebblingLean.Hypercube.PaperParameters
theorem _root_.solution {A K : ℝ} {n : ℕ}
    (hA : 0 ≤ A) :
    (annulusWidthCore A K n) ^ 2 ≤
      (annulusWidth A K n : ℝ) ^ 2 := by
  have hcore_nonneg :=
    annulusWidthCore_nonneg_of_A_nonneg (A := A) (K := K) (n := n) hA
  have hwidth_nonneg : 0 ≤ (annulusWidth A K n : ℝ) := by positivity
  exact (sq_le_sq₀ hcore_nonneg hwidth_nonneg).mpr
    (annulusWidthCore_le_width_real (A := A) (K := K) (n := n))
end PebblingLean.Hypercube.PaperParameters
