-- Prove2me | solution 1 for ThreeSum.Parameters.entropy_tangent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:00:39.293848+00:00
-- url     : https://prove2.me/submissions/97e6f589-5cd9-4823-95f4-a9891055b86b

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_Parameters
import Theorems.Thm_ThreeSum_Parameters_log_two_pos

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.Parameters
open Set Real
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
namespace ThreeSum.Parameters
theorem _root_.solution {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    entropy t ≤ tangentA + tangentB * t := by
  have hu : (17 / 100 : ℝ) ∈ Icc (0 : ℝ) 1 := by constructor <;> norm_num
  have hd := Real.hasDerivAt_binEntropy (p := (17 / 100 : ℝ)) (by norm_num) (by norm_num)
  have hconc := Real.strictConcave_binEntropy.concaveOn
  have htan : Real.binEntropy t ≤ Real.binEntropy (17 / 100) +
      (t - 17 / 100) * (Real.log (1 - 17 / 100) - Real.log (17 / 100)) := by
    rcases lt_trichotomy t (17 / 100) with h | h | h
    · have hs := hconc.le_slope_of_hasDerivAt ht hu h hd
      rw [slope_def_field, le_div_iff₀ (sub_pos.mpr h)] at hs
      nlinarith
    · subst t
      simp
    · have hs := hconc.slope_le_of_hasDerivAt hu ht h hd
      rw [slope_def_field, div_le_iff₀ (sub_pos.mpr h)] at hs
      nlinarith
  have heq : Real.binEntropy (17 / 100) +
      (t - 17 / 100) * (Real.log (1 - 17 / 100) - Real.log (17 / 100)) =
      Real.log 100 - Real.log 83 + t * (Real.log 83 - Real.log 17) := by
    norm_num [Real.binEntropy]
    rw [Real.log_div (by norm_num : (100 : ℝ) ≠ 0) (by norm_num : (17 : ℝ) ≠ 0),
      Real.log_div (by norm_num : (100 : ℝ) ≠ 0) (by norm_num : (83 : ℝ) ≠ 0),
      Real.log_div (by norm_num : (83 : ℝ) ≠ 0) (by norm_num : (100 : ℝ) ≠ 0),
      Real.log_div (by norm_num : (17 : ℝ) ≠ 0) (by norm_num : (100 : ℝ) ≠ 0)]
    ring
  rw [heq] at htan
  unfold entropy tangentA tangentB
  have hdiv := div_le_div_of_nonneg_right htan log_two_pos.le
  apply le_of_le_of_eq hdiv
  ring
end ThreeSum.Parameters
