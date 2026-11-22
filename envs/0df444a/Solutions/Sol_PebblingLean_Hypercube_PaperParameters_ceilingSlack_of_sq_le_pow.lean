-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.ceilingSlack_of_sq_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:12:08.150797+00:00
-- url     : https://prove2.me/submissions/42d2119f-5ecd-45e4-8d61-e169cd5acae0

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
    (hn : 0 < n)
    (hpow : (n : ℝ) ^ 2 ≤ (((4 : ℝ) / 3) ^ splitA K n)) :
    1 ≤ loss n * (((4 : ℝ) / 3) ^ splitA K n) := by
  unfold loss
  have hn_sq_pos : 0 < (n : ℝ) ^ 2 := by positivity
  calc
    1 = ((n : ℝ) ^ 2)⁻¹ * ((n : ℝ) ^ 2) := by
      field_simp [hn_sq_pos.ne']
    _ ≤ ((n : ℝ) ^ 2)⁻¹ * (((4 : ℝ) / 3) ^ splitA K n) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
end PebblingLean.Hypercube.PaperParameters
