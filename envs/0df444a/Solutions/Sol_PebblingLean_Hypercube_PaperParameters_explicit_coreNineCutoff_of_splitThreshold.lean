-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.explicit_coreNineCutoff_of_splitThreshold
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:12:54.480844+00:00
-- url     : https://prove2.me/submissions/049093fd-b87f-413c-8083-cccd17a0ddfe

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
    81 ≤ (4 : ℝ) ^ 2 * (((3 : ℝ) * (n0 : ℝ) / 4) *
      Real.log (n0 : ℝ)) := by
  have hn12 : (12 : ℝ) ≤ (n0 : ℝ) := by
    have hbig : (12 : ℝ) ≤ (128 * (217 : ℝ) ^ 2) ^ 2 := by norm_num
    exact hbig.trans hsplitThreshold
  have hn2 : (2 : ℝ) ≤ (n0 : ℝ) := by linarith
  have hlog2Lower : (3 : ℝ) / 5 ≤ Real.log 2 := by
    have h := Real.log_two_gt_d9
    norm_num at h ⊢
    linarith
  have hlog2le : Real.log 2 ≤ Real.log (n0 : ℝ) :=
    Real.log_le_log (by norm_num : (0 : ℝ) < 2) hn2
  have hlogLower : (3 : ℝ) / 5 ≤ Real.log (n0 : ℝ) :=
    hlog2Lower.trans hlog2le
  nlinarith
end PebblingLean.Hypercube.PaperParameters
