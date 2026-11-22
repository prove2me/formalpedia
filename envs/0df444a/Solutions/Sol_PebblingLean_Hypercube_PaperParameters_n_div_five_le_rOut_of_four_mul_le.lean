-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.n_div_five_le_rOut_of_four_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:07:51.250335+00:00
-- url     : https://prove2.me/submissions/5ff21a2d-490d-4803-b715-0f7e25de4b65

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_splitA_div_three_le_rOut
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_n_div_five_le_splitA_div_three_of_four_mul_le

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters
namespace PebblingLean.Hypercube.PaperParameters
theorem _root_.solution {A K : ℝ} {n : ℕ}
    (hquarter : 4 * splitM K n ≤ n) :
    n / 5 ≤ rOut A K n := by
  calc
    n / 5 ≤ splitA K n / 3 :=
      n_div_five_le_splitA_div_three_of_four_mul_le hquarter
    _ ≤ rOut A K n := splitA_div_three_le_rOut
end PebblingLean.Hypercube.PaperParameters
