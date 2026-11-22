-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.one_twentieth_le_stackMargin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:58:58.650472+00:00
-- url     : https://prove2.me/submissions/abf2cc87-6626-41cb-b4b8-93d747da1f98

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
theorem _root_.solution : (1 : ℝ) / 20 ≤ stackMargin := by
  have hlogLower : (5 : ℝ) / 32 ≤ Real.log ((32 : ℝ) / 27) := by
    have h :=
      Real.one_sub_inv_le_log_of_pos
        (by norm_num : (0 : ℝ) < (32 : ℝ) / 27)
    norm_num at h ⊢
    exact h
  have htriple : 3 * stackMargin = Real.log ((32 : ℝ) / 27) := by
    rw [stackMargin]
    rw [show (32 : ℝ) / 27 = ((4 : ℝ) / 3) ^ 3 / 2 by norm_num]
    rw [Real.log_div
      (by norm_num : (((4 : ℝ) / 3) ^ 3) ≠ 0)
      (by norm_num : (2 : ℝ) ≠ 0)]
    rw [Real.log_pow]
    ring_nf
  nlinarith
end PebblingLean.Hypercube.PaperParameters
