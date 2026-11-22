-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.sq_growth_step_for_four_thirds_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:12:15.31033+00:00
-- url     : https://prove2.me/submissions/9282d9fa-5a70-4b7e-be1c-4a2646a024fa

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
theorem _root_.solution (n : ℕ) (hn : 14 ≤ n) :
    ((n + 2 : ℕ) : ℝ) ^ 2 ≤ ((4 : ℝ) / 3) * (n : ℝ) ^ 2 := by
  have hn_real : (14 : ℝ) ≤ n := by exact_mod_cast hn
  norm_num
  nlinarith [sq_nonneg ((n : ℝ) - 6)]
end PebblingLean.Hypercube.PaperParameters
