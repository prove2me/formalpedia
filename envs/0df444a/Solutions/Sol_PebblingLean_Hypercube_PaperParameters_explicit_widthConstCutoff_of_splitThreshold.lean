-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.explicit_widthConstCutoff_of_splitThreshold
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:12:58.133294+00:00
-- url     : https://prove2.me/submissions/ae20e619-2582-43fb-b63f-42513d9f571d

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_log_two_le_one

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters
namespace PebblingLean.Hypercube.PaperParameters
theorem _root_.solution {n0 : ℕ}
    (hsplitThreshold : (128 * (217 : ℝ) ^ 2) ^ 2 ≤ (n0 : ℝ)) :
    Real.log 128 + 4 * Real.log 2 ≤
      ((217 : ℝ) / 30 * Real.log 2) *
        Real.sqrt ((n0 : ℝ) * Real.log (n0 : ℝ)) := by
  have hn15 : (15 : ℝ) ≤ (n0 : ℝ) :=
    (by norm_num : (15 : ℝ) ≤ (128 * (217 : ℝ) ^ 2) ^ 2).trans hsplitThreshold
  have hlogLower : (3 : ℝ) / 5 ≤ Real.log (n0 : ℝ) :=
    (by linarith only [Real.log_two_gt_d9] : (3 : ℝ) / 5 ≤ Real.log 2).trans
      (Real.log_le_log (by norm_num) (by linarith only [hn15]))
  have hsqrtLower : (3 : ℝ) ≤ Real.sqrt ((n0 : ℝ) * Real.log (n0 : ℝ)) :=
    Real.le_sqrt_of_sq_le (calc
      (3 : ℝ) ^ 2 = 15 * (3 / 5) := by norm_num
      _ ≤ (n0 : ℝ) * Real.log (n0 : ℝ) :=
        mul_le_mul hn15 hlogLower (by norm_num) (Nat.cast_nonneg _))
  have hcoeffLower : (5 : ℝ) ≤ (217 : ℝ) / 30 * Real.log 2 := by
    linarith only [Real.log_two_gt_d9]
  have hlhs : Real.log 128 + 4 * Real.log 2 ≤ 11 := by
    rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]
    norm_num
    linarith only [log_two_le_one]
  calc
    Real.log 128 + 4 * Real.log 2 ≤ 11 := hlhs
    _ ≤ 5 * 3 := by norm_num
    _ ≤ ((217 : ℝ) / 30 * Real.log 2) *
        Real.sqrt ((n0 : ℝ) * Real.log (n0 : ℝ)) :=
      mul_le_mul hcoeffLower hsqrtLower (by norm_num) (by linarith only [hcoeffLower])
end PebblingLean.Hypercube.PaperParameters
