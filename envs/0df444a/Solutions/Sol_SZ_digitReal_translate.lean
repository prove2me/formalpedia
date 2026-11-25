-- Prove2me | solution 1 for SZ.digitReal_translate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:29:01.468209+00:00
-- url     : https://prove2.me/submissions/6f4b3bfb-f9aa-4175-9c10-1aa7f9197238

import Definitions.Def_SZ_DigitParity
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_CoverGame
import Theorems.Thm_SZ_W_mem
import Theorems.Thm_SZ_W_eq_residual
import Theorems.Thm_SZ_isDigits_digitA
import Theorems.Thm_SZ_isDigits_digitB
import Theorems.Thm_SZ_digitSum_tendsto


set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution :
    digitReal 3 digitA + Real.sqrt 3 * digitReal 3 digitB = 3 * Real.sqrt 3 - 4 := by
  have hlim : Tendsto (fun k => digitSum 3 digitA k + Real.sqrt 3 * digitSum 3 digitB k)
      atTop (𝓝 (digitReal 3 digitA + Real.sqrt 3 * digitReal 3 digitB)) :=
    (digitSum_tendsto isDigits_digitA).add
      (tendsto_const_nhds.mul (digitSum_tendsto isDigits_digitB))
  have hzero : Tendsto (fun k : ℕ => (3 * Real.sqrt 3 - 4)
      - (digitSum 3 digitA k + Real.sqrt 3 * digitSum 3 digitB k)) atTop (𝓝 0) := by
    refine squeeze_zero (g := fun k : ℕ => (3 + 3 * Real.sqrt 3) / 3 ^ (k + 1))
      (fun k => ?_) (fun k => ?_) ?_
    · have h := (W_mem k).1
      rw [W_eq_residual k] at h
      have hp : (0:ℝ) < 3 ^ (k + 1) := by positivity
      nlinarith
    · have h := (W_mem k).2
      rw [W_eq_residual k] at h
      have hp : (0:ℝ) < 3 ^ (k + 1) := by positivity
      rw [le_div_iff₀ hp]
      nlinarith
    · have hmain : Tendsto (fun k : ℕ => (3 + 3 * Real.sqrt 3) * (1 / 3 : ℝ) ^ (k + 1))
          atTop (𝓝 0) := by
        have hg : Tendsto (fun k : ℕ => (1 / 3 : ℝ) ^ (k + 1)) atTop (𝓝 0) := by
          have h0 := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1/3 : ℝ))
            (by norm_num) (by norm_num)
          exact h0.comp (Filter.tendsto_add_atTop_nat 1)
        simpa using hg.const_mul (3 + 3 * Real.sqrt 3)
      refine hmain.congr fun k => ?_
      rw [div_pow, one_pow]
      ring
  have hlim2 : Tendsto (fun k => digitSum 3 digitA k + Real.sqrt 3 * digitSum 3 digitB k)
      atTop (𝓝 (3 * Real.sqrt 3 - 4)) := by
    have h := (tendsto_const_nhds (x := (3 * Real.sqrt 3 - 4)) (f := atTop (α := ℕ))).sub hzero
    simpa using h
  exact tendsto_nhds_unique hlim hlim2
end SZ
