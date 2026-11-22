-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.n_div_five_le_splitA_div_three_of_four_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:06:52.544829+00:00
-- url     : https://prove2.me/submissions/adbe2f44-201b-4ae7-af83-89326d515de3

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
theorem _root_.solution {K : ℝ} {n : ℕ}
    (hquarter : 4 * splitM K n ≤ n) :
    n / 5 ≤ splitA K n / 3 := by
  unfold splitA
  omega
end PebblingLean.Hypercube.PaperParameters
