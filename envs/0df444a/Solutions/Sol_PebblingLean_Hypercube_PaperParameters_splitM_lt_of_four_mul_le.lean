-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.splitM_lt_of_four_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:55:53.270439+00:00
-- url     : https://prove2.me/submissions/f80fbab7-8854-4cd9-90e8-31a916f98351

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
theorem _root_.solution {K : ℝ} {n0 n : ℕ}
    (hn0_pos : 0 < n0) (hn : n0 ≤ n)
    (hquarter : 4 * splitM K n ≤ n) :
    splitM K n < n := by
  have hn_pos : 0 < n := lt_of_lt_of_le hn0_pos hn
  omega
end PebblingLean.Hypercube.PaperParameters
