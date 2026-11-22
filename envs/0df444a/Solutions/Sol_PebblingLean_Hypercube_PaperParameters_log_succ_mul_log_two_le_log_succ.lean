-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.log_succ_mul_log_two_le_log_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:09:45.635668+00:00
-- url     : https://prove2.me/submissions/1df6f15d-1d58-4005-9fc8-f13eff8d62e0

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
theorem _root_.solution {n : ℕ} :
    Real.log ((((n + 1 : ℕ) : ℝ) * Real.log 2)) ≤
      Real.log (((n + 1 : ℕ) : ℝ)) := by
  have hlog2_pos : 0 < Real.log 2 :=
    Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have harg_pos : 0 < (((n + 1 : ℕ) : ℝ) * Real.log 2) := by
    positivity
  have hn_nonneg : 0 ≤ ((n + 1 : ℕ) : ℝ) := by positivity
  have hle :
      ((n + 1 : ℕ) : ℝ) * Real.log 2 ≤ ((n + 1 : ℕ) : ℝ) := by
    calc
      ((n + 1 : ℕ) : ℝ) * Real.log 2
          ≤ ((n + 1 : ℕ) : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left log_two_le_one hn_nonneg
      _ = ((n + 1 : ℕ) : ℝ) := by ring
  exact Real.log_le_log harg_pos hle
end PebblingLean.Hypercube.PaperParameters
