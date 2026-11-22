-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.rOut_real_le_div_three_add_widthCore_add_one_of_A_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:10:28.871796+00:00
-- url     : https://prove2.me/submissions/43462d18-6c0d-424d-9a77-dfe2a12639a6

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_annulusWidth_real_le_core_add_one_of_A_nonneg

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters
namespace PebblingLean.Hypercube.PaperParameters
theorem _root_.solution
    {A K : ℝ} {n : ℕ} (hA : 0 ≤ A) :
    (rOut A K n : ℝ) ≤
      ((splitA K n / 3 : ℕ) : ℝ) + annulusWidthCore A K n + 1 := by
  unfold rOut
  rw [Nat.cast_add]
  have hwidth :=
    annulusWidth_real_le_core_add_one_of_A_nonneg
      (A := A) (K := K) (n := n) hA
  linarith
end PebblingLean.Hypercube.PaperParameters
