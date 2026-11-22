-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.splitA_add_splitM_of_four_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:55:36.927811+00:00
-- url     : https://prove2.me/submissions/61b51fba-4c36-46df-bb3d-fe85b30e8c68

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
    splitA K n + splitM K n = n := by
  unfold splitA
  have hmle : splitM K n ≤ n := by omega
  exact Nat.sub_add_cancel hmle
end PebblingLean.Hypercube.PaperParameters
