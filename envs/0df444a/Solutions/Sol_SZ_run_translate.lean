-- Prove2me | solution 1 for SZ.run_translate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:16:16.933119+00:00
-- url     : https://prove2.me/submissions/503bd8fd-1af7-4797-a9d8-f3c5de5eb21d

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
import Theorems.Thm_SZ_runVal_mem
import Theorems.Thm_SZ_runVal_eq_residual
import Theorems.Thm_SZ_isDigits_run_fst
import Theorems.Thm_SZ_isDigits_run_snd
import Theorems.Thm_SZ_digitSum_tendsto

section
namespace SZ
open Filter Topology
private theorem t3_lb : (1.7 : ℝ) < Real.sqrt 3 :=
  (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
private theorem t3_ub : Real.sqrt 3 < 1.8 := by
  have h : Real.sqrt 3 < Real.sqrt (1.8 ^ 2) := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1.8)] at h
end SZ
end

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution {d : ℕ → ℤ × ℤ} (hrun : IsRun (-12, 9) d) :
    digitReal 3 (fun i => (d i).1) + Real.sqrt 3 * digitReal 3 (fun i => (d i).2)
      = 3 * Real.sqrt 3 - 4 := by
  have h0 : (0 : ℝ) ≤ valS ((-12 : ℤ), (9 : ℤ)) := by
    rw [valS]; push_cast; linarith [t3_lb]
  have h1 : valS ((-12 : ℤ), (9 : ℤ)) ≤ 3 + 3 * Real.sqrt 3 := by
    rw [valS]; push_cast; linarith [t3_ub]
  have hlim : Tendsto (fun k => digitSum 3 (fun i => (d i).1) k
      + Real.sqrt 3 * digitSum 3 (fun i => (d i).2) k) atTop
      (𝓝 (digitReal 3 (fun i => (d i).1) + Real.sqrt 3 * digitReal 3 (fun i => (d i).2))) :=
    (digitSum_tendsto (isDigits_run_fst hrun)).add
      (tendsto_const_nhds.mul (digitSum_tendsto (isDigits_run_snd hrun)))
  have hzero : Tendsto (fun k : ℕ => (3 * Real.sqrt 3 - 4)
      - (digitSum 3 (fun i => (d i).1) k
          + Real.sqrt 3 * digitSum 3 (fun i => (d i).2) k)) atTop (𝓝 0) := by
    refine squeeze_zero (g := fun k : ℕ => (3 + 3 * Real.sqrt 3) / 3 ^ (k + 1))
      (fun k => ?_) (fun k => ?_) ?_
    · have h := (runVal_mem hrun h0 h1 k).1
      rw [runVal_eq_residual d k] at h
      have hp : (0:ℝ) < 3 ^ (k + 1) := by positivity
      nlinarith
    · have h := (runVal_mem hrun h0 h1 k).2
      rw [runVal_eq_residual d k] at h
      have hp : (0:ℝ) < 3 ^ (k + 1) := by positivity
      rw [le_div_iff₀ hp]
      nlinarith
    · have hmain : Tendsto (fun k : ℕ => (3 + 3 * Real.sqrt 3) * (1 / 3 : ℝ) ^ (k + 1))
          atTop (𝓝 0) := by
        have hg : Tendsto (fun k : ℕ => (1 / 3 : ℝ) ^ (k + 1)) atTop (𝓝 0) := by
          have h0' := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1/3 : ℝ))
            (by norm_num) (by norm_num)
          exact h0'.comp (Filter.tendsto_add_atTop_nat 1)
        simpa using hg.const_mul (3 + 3 * Real.sqrt 3)
      refine hmain.congr fun k => ?_
      rw [div_pow, one_pow]
      ring
  have hlim2 : Tendsto (fun k => digitSum 3 (fun i => (d i).1) k
      + Real.sqrt 3 * digitSum 3 (fun i => (d i).2) k) atTop (𝓝 (3 * Real.sqrt 3 - 4)) := by
    have h := (tendsto_const_nhds (x := (3 * Real.sqrt 3 - 4)) (f := atTop (α := ℕ))).sub hzero
    simpa using h
  exact tendsto_nhds_unique hlim hlim2
end SZ
