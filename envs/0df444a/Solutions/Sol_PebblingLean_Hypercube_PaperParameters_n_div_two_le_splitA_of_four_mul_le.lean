-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.n_div_two_le_splitA_of_four_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:07:53.416009+00:00
-- url     : https://prove2.me/submissions/8cd9f495-d365-41af-b238-39cad7e2362f

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
    n / 2 ≤ splitA K n := by
  unfold splitA
  omega
end PebblingLean.Hypercube.PaperParameters
