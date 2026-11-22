-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.three_width_le_splitA_of_core_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:09:13.66628+00:00
-- url     : https://prove2.me/submissions/a8f208d1-0b50-44be-9626-614313669415

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
    (hA : 0 ≤ A)
    (hcore :
      3 * (annulusWidthCore A K n + 1) ≤ (splitA K n : ℝ)) :
    3 * annulusWidth A K n ≤ splitA K n := by
  have hcore_nonneg :=
    annulusWidthCore_nonneg_of_A_nonneg (A := A) (K := K) (n := n) hA
  have hwidth_le :
      (annulusWidth A K n : ℝ) ≤ annulusWidthCore A K n + 1 :=
    annulusWidth_real_le_core_add_one hcore_nonneg
  have hreal :
      (3 : ℝ) * (annulusWidth A K n : ℝ) ≤ (splitA K n : ℝ) := by
    have hmul :
        (3 : ℝ) * (annulusWidth A K n : ℝ) ≤
          3 * (annulusWidthCore A K n + 1) :=
      mul_le_mul_of_nonneg_left hwidth_le (by norm_num : (0 : ℝ) ≤ 3)
    exact hmul.trans hcore
  exact_mod_cast hreal
end PebblingLean.Hypercube.PaperParameters
