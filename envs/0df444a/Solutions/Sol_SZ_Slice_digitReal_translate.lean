-- Prove2me | solution 1 for SZ.Slice.digitReal_translate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:38:43.603035+00:00
-- url     : https://prove2.me/submissions/535af466-c04b-4cc5-860c-0f78175ad42b

import Definitions.Def_SZ_Defs
import Definitions.Def_SZ_DigitParity
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Definitions.Def_SZ_Slice
import Theorems.Thm_SZ_Slice_three_le_cast
import Theorems.Thm_SZ_Slice_W_mem
import Theorems.Thm_SZ_Slice_isDigits_dA
import Theorems.Thm_SZ_Slice_isDigits_dB
import Theorems.Thm_SZ_Slice_W_eq_residual
import Theorems.Thm_SZ_digitSum_tendsto


set_option autoImplicit false
open SZ
open Filter Topology
open SZ.Slice
variable (S : Slice)
variable {S}
namespace SZ.Slice
theorem _root_.solution (S : Slice) {σ : ℝ} (h0 : 0 ≤ σ) (h1 : σ ≤ S.U) :
    digitReal S.m (S.dA ((S.m : ℝ) * σ)) + S.sq * digitReal S.m (S.dB ((S.m : ℝ) * σ)) = σ := by
  have hm : (0 : ℝ) < (S.m : ℝ) := by have := S.three_le_cast; linarith
  have hm1 : (1 : ℝ) < (S.m : ℝ) := by have := S.three_le_cast; linarith
  have hw0 : 0 ≤ (S.m : ℝ) * σ := mul_nonneg hm.le h0
  have hw1 : (S.m : ℝ) * σ ≤ (S.m : ℝ) * S.U := mul_le_mul_of_nonneg_left h1 hm.le
  have hA := isDigits_dA hw0 hw1
  have hB := isDigits_dB hw0 hw1
  have hlim : Tendsto (fun k => digitSum S.m (S.dA ((S.m : ℝ) * σ)) k
      + S.sq * digitSum S.m (S.dB ((S.m : ℝ) * σ)) k) atTop
      (𝓝 (digitReal S.m (S.dA ((S.m : ℝ) * σ)) + S.sq * digitReal S.m (S.dB ((S.m : ℝ) * σ)))) :=
    (digitSum_tendsto hA).add (tendsto_const_nhds.mul (digitSum_tendsto hB))
  have hzero : Tendsto (fun k : ℕ => σ - (digitSum S.m (S.dA ((S.m : ℝ) * σ)) k
      + S.sq * digitSum S.m (S.dB ((S.m : ℝ) * σ)) k)) atTop (𝓝 0) := by
    refine squeeze_zero (g := fun k : ℕ => ((S.m : ℝ) * S.U) / (S.m : ℝ) ^ (k + 1))
      (fun k => ?_) (fun k => ?_) ?_
    · have h := (W_mem hw0 hw1 k).1
      rw [W_eq_residual S σ k] at h
      have hp : (0 : ℝ) < (S.m : ℝ) ^ (k + 1) := by positivity
      nlinarith
    · have h := (W_mem hw0 hw1 k).2
      rw [W_eq_residual S σ k] at h
      have hp : (0 : ℝ) < (S.m : ℝ) ^ (k + 1) := by positivity
      rw [le_div_iff₀ hp]
      nlinarith
    · have hg : Tendsto (fun k : ℕ => (1 / (S.m : ℝ)) ^ (k + 1)) atTop (𝓝 0) := by
        have h0' := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / (S.m : ℝ)))
          (by positivity) ((div_lt_one hm).mpr hm1)
        exact h0'.comp (Filter.tendsto_add_atTop_nat 1)
      have hmain : Tendsto (fun k : ℕ => ((S.m : ℝ) * S.U) * (1 / (S.m : ℝ)) ^ (k + 1))
          atTop (𝓝 0) := by simpa using hg.const_mul ((S.m : ℝ) * S.U)
      refine hmain.congr fun k => ?_
      rw [div_pow, one_pow]
      ring
  have hlim2 : Tendsto (fun k => digitSum S.m (S.dA ((S.m : ℝ) * σ)) k
      + S.sq * digitSum S.m (S.dB ((S.m : ℝ) * σ)) k) atTop (𝓝 σ) := by
    have h := (tendsto_const_nhds (x := σ) (f := atTop (α := ℕ))).sub hzero
    simpa using h
  exact tendsto_nhds_unique hlim hlim2
end SZ.Slice
