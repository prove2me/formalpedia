-- Prove2me | solution 1 for ThreeSum.Parameters.gamma_formula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:07:20.167448+00:00
-- url     : https://prove2.me/submissions/68555a7e-c8dc-4e8e-a9dc-e26e9df3262f

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_Parameters
import Theorems.Thm_ThreeSum_Parameters_entropy_eq

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.Parameters
open Set Real
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
namespace ThreeSum.Parameters
theorem _root_.solution {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (1 / 2)) :
    gamma t = gammaNumerator t / Real.log 2 := by
  have h1 : (1 - t : ℝ) ≠ 0 := by linarith [ht.2]
  have h255 : (255 + t : ℝ) ≠ 0 := by linarith [ht.1]
  unfold gamma
  rw [entropy_eq, entropy_eq]
  rw [show 1 - (1 - t) / 256 = (255 + t) / 256 by ring]
  norm_num
  rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (256 : ℝ) ≠ 0),
    Real.log_div (by norm_num : (255 : ℝ) ≠ 0) (by norm_num : (256 : ℝ) ≠ 0),
    Real.log_div h1 (by norm_num : (256 : ℝ) ≠ 0),
    Real.log_div h255 (by norm_num : (256 : ℝ) ≠ 0)]
  simp only [Real.log_one]
  unfold gammaNumerator
  ring
end ThreeSum.Parameters
