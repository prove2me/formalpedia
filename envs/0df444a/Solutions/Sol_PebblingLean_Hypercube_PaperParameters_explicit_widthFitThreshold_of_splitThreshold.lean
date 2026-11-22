-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.explicit_widthFitThreshold_of_splitThreshold
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:12:53.744335+00:00
-- url     : https://prove2.me/submissions/07a93088-c402-446b-99c6-e5c772e21ba4

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
theorem _root_.solution {n0 : ℕ}
    (hsplitThreshold : (128 * (217 : ℝ) ^ 2) ^ 2 ≤ (n0 : ℝ)) :
    (128 * ((4 : ℝ) * Real.sqrt 3) ^ 2) ^ 2 ≤ (n0 : ℝ) := by
  have hsqrt3_le_two : Real.sqrt 3 ≤ (2 : ℝ) := by
    rw [Real.sqrt_le_iff]
    constructor <;> norm_num
  have hmul_nonneg : 0 ≤ (4 : ℝ) * Real.sqrt 3 := by positivity
  have hmul_le : (4 : ℝ) * Real.sqrt 3 ≤ 8 := by
    nlinarith
  have hmul_sq :
      ((4 : ℝ) * Real.sqrt 3) ^ 2 ≤ 8 ^ 2 :=
    (sq_le_sq₀ hmul_nonneg (by norm_num : (0 : ℝ) ≤ 8)).mpr hmul_le
  have hcoef :
      128 * ((4 : ℝ) * Real.sqrt 3) ^ 2 ≤
        128 * (217 : ℝ) ^ 2 := by
    nlinarith
  have hcoef_nonneg :
      0 ≤ 128 * ((4 : ℝ) * Real.sqrt 3) ^ 2 := by positivity
  have htarget_nonneg : 0 ≤ 128 * (217 : ℝ) ^ 2 := by norm_num
  have hsq :
      (128 * ((4 : ℝ) * Real.sqrt 3) ^ 2) ^ 2 ≤
        (128 * (217 : ℝ) ^ 2) ^ 2 :=
    (sq_le_sq₀ hcoef_nonneg htarget_nonneg).mpr hcoef
  exact hsq.trans hsplitThreshold
end PebblingLean.Hypercube.PaperParameters
