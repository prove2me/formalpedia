-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.splitA_real_eq_sub_of_four_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:07:32.608637+00:00
-- url     : https://prove2.me/submissions/98e40187-3d3f-414e-831f-98483ed28f94

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
    (splitA K n : ℝ) = (n : ℝ) - (splitM K n : ℝ) := by
  unfold splitA
  have hmle : splitM K n ≤ n := by omega
  exact Nat.cast_sub hmle
end PebblingLean.Hypercube.PaperParameters
