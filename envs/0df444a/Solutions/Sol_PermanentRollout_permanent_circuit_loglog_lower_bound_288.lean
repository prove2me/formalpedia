-- Prove2me | solution 1 for PermanentRollout.permanent_circuit_loglog_lower_bound_288
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:11.481307+00:00
-- url     : https://prove2.me/submissions/acac9f2c-a403-4567-8164-1075a79ae13c

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_permanent_circuit_loglog_lower_bound

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace PermanentRollout
theorem _root_.solution {n : ℕ} (hn : 2 ^ 64 ≤ n) :
    (1 / 288 : ℝ) * (n : ℝ) ^ 2 * Real.logb 2 (Real.logb 2 (n : ℝ)) ≤
      (circuitComplexity (permanent n) : ℝ) := by
  have hnmain : 2 ^ 16 ≤ n := by
    have hthreshold : (2 : ℕ) ^ 16 ≤ 2 ^ 64 := by norm_num
    exact hthreshold.trans hn
  have hinner : (64 : ℝ) ≤ Real.logb 2 (n : ℝ) := by
    calc
      (64 : ℝ) = Real.logb 2 ((2 : ℝ) ^ (64 : ℕ)) := by
        rw [Real.logb_pow]
        norm_num
      _ ≤ Real.logb 2 (n : ℝ) := by
        apply Real.logb_le_logb_of_le (by norm_num) (by positivity)
        exact_mod_cast hn
  have houter : (6 : ℝ) ≤ Real.logb 2 (Real.logb 2 (n : ℝ)) := by
    calc
      (6 : ℝ) = Real.logb 2 ((2 : ℝ) ^ (6 : ℕ)) := by
        rw [Real.logb_pow]
        norm_num
      _ ≤ Real.logb 2 (Real.logb 2 (n : ℝ)) := by
        apply Real.logb_le_logb_of_le (by norm_num) (by norm_num)
        norm_num
        exact hinner
  have hcoefficient :
      Real.logb 2 (Real.logb 2 (n : ℝ)) / 288 ≤
        (Real.logb 2 (Real.logb 2 (n : ℝ)) - 3) / 144 := by
    linarith
  have hproduct := mul_le_mul_of_nonneg_left hcoefficient
    (sq_nonneg (n : ℝ))
  calc
    (1 / 288 : ℝ) * (n : ℝ) ^ 2 * Real.logb 2 (Real.logb 2 (n : ℝ)) ≤
        (n : ℝ) ^ 2 * (Real.logb 2 (Real.logb 2 (n : ℝ)) - 3) / 144 := by
          nlinarith
    _ ≤ (circuitComplexity (permanent n) : ℝ) :=
      permanent_circuit_loglog_lower_bound hnmain
end PermanentRollout
