-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.ceilingSq_of_pow_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:12:14.256799+00:00
-- url     : https://prove2.me/submissions/3a7c763c-1930-4da7-9288-56d4d07f3665

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
    (hhalf : n / 2 ≤ splitA K n)
    (hpow : (n : ℝ) ^ 2 ≤ (((4 : ℝ) / 3) ^ (n / 2))) :
    (n : ℝ) ^ 2 ≤ (((4 : ℝ) / 3) ^ splitA K n) := by
  have hbase : (1 : ℝ) ≤ ((4 : ℝ) / 3) := by norm_num
  exact hpow.trans (pow_le_pow_right₀ hbase hhalf)
end PebblingLean.Hypercube.PaperParameters
