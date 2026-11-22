-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.four_mul_splitM_le_of_real_le_quarter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:55:44.417007+00:00
-- url     : https://prove2.me/submissions/901ee38f-c0bb-481a-8873-fe163fcf0724

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
    (hreal : (splitM K n : ℝ) ≤ (n : ℝ) / 4) :
    4 * splitM K n ≤ n := by
  have hreal' : ((4 * splitM K n : ℕ) : ℝ) ≤ (n : ℝ) := by
    norm_num
    linarith
  exact_mod_cast hreal'
end PebblingLean.Hypercube.PaperParameters
