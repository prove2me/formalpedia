-- Prove2me | solution 1 for Sqrt6KissingBound.dimension_mul_two_pow_le_sqrt6_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:20:56.529809+00:00
-- url     : https://prove2.me/submissions/66a3da0b-1a88-44a0-81c7-cd1a0ba2cfd6

import Definitions.Def_Sqrt6KissingBound_CenteredBicone
import Definitions.Def_Sqrt6KissingBound_BallVolumes
import Definitions.Def_Sqrt6KissingBound_BiconeBounds
import Theorems.Thm_Sqrt6KissingBound_inner_standardAxis_standardCoordinates
import Theorems.Thm_Sqrt6KissingBound_mem_tailBall
import Theorems.Thm_Sqrt6KissingBound_norm_standardAxis
attribute [local simp] Sqrt6KissingBound.inner_standardAxis_standardCoordinates
attribute [local simp] Sqrt6KissingBound.mem_tailBall
attribute [local simp] Sqrt6KissingBound.norm_standardAxis



set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
namespace Sqrt6KissingBound
theorem _root_.solution :
    ∀ n : ℕ, 6 ≤ n → (n : ℝ) * (2 : ℝ) ^ (n - 1) ≤ (Real.sqrt 6) ^ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    have hsquare : (Real.sqrt 6) ^ 2 = 6 := by norm_num
    by_cases h6 : n = 6
    · subst n
      rw [show (Real.sqrt 6) ^ 6 = ((Real.sqrt 6) ^ 2) ^ 3 by ring, hsquare]
      norm_num
    by_cases h7 : n = 7
    · subst n
      have hs0 : 0 ≤ Real.sqrt 6 := Real.sqrt_nonneg _
      have hs : (56 : ℝ) / 27 < Real.sqrt 6 := by
        apply (sq_lt_sq₀ (by norm_num) hs0).1
        rw [hsquare]
        norm_num
      rw [show (Real.sqrt 6) ^ 7 = ((Real.sqrt 6) ^ 2) ^ 3 * Real.sqrt 6 by ring, hsquare]
      norm_num
      nlinarith
    have hn8 : 8 ≤ n := by omega
    have hprev := ih (n - 2) (by omega) (by omega)
    have hpow2 : (2 : ℝ) ^ (n - 1) = 4 * (2 : ℝ) ^ (n - 3) := by
      rw [show n - 1 = (n - 3) + 2 by omega, pow_add]
      norm_num
      ring
    have hsqrtn : (Real.sqrt 6) ^ n = 6 * (Real.sqrt 6) ^ (n - 2) := by
      have h := pow_add (Real.sqrt 6) (n - 2) 2
      rw [hsquare] at h
      simpa only [show n - 2 + 2 = n by omega, mul_comm] using h
    have hprev' : ((n - 2 : ℕ) : ℝ) * (2 : ℝ) ^ (n - 3) ≤
        (Real.sqrt 6) ^ (n - 2) := by
      simpa only [show (n - 2) - 1 = n - 3 by omega] using hprev
    have hcoef : (4 : ℝ) * n ≤ 6 * (n - 2 : ℕ) := by
      exact_mod_cast (show 4 * n ≤ 6 * (n - 2) by omega)
    rw [hpow2, hsqrtn]
    calc
      (n : ℝ) * (4 * (2 : ℝ) ^ (n - 3)) = (4 * n) * (2 : ℝ) ^ (n - 3) := by ring
      _ ≤ (6 * (n - 2 : ℕ)) * (2 : ℝ) ^ (n - 3) :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ = 6 * (((n - 2 : ℕ) : ℝ) * (2 : ℝ) ^ (n - 3)) := by ring
      _ ≤ 6 * (Real.sqrt 6) ^ (n - 2) := mul_le_mul_of_nonneg_left hprev' (by norm_num)
end Sqrt6KissingBound
