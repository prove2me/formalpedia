-- Prove2me | solution 1 for ThreeSum.Scales.primeLoss_log_ratio_tendsto_zero_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:23:29.415853+00:00
-- url     : https://prove2.me/submissions/34d577a7-bfcc-43f2-b724-c201cc1df6e8

import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_ThreeSum_Asymptotics
import Definitions.Def_Submission_ThreeSum_PrimeDensity
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Sqrt
import Definitions.Def_Submission_ThreeSum_Scales
import Theorems.Thm_ThreeSum_Scales_primeWindow_ge_two
import Theorems.Thm_ThreeSum_Scales_primeWindow_log_ratio_tendsto_zero
import Definitions.Def_WeightedCache3SUM_Alias_5892d665e4005f14
import Theorems.Thm_ThreeSum_Asymptotics_log_nat_tendsto_atTop
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices



set_option autoImplicit false
open ThreeSum ThreeSum.Scales
open Filter Real
open scoped Topology
noncomputable section
namespace ThreeSum.Scales
theorem _root_.solution :
    Tendsto (fun n : ℕ => Real.log (primeLoss radix n : ℝ) / Real.log n) atTop (𝓝 0) := by
  have hc := Asymptotics.log_nat_tendsto_atTop.inv_tendsto_atTop.const_mul (Real.log 32)
  have hd := primeDepth_log_ratio_tendsto_zero.const_mul (Real.log 4)
  have h := (hc.add primeWindow_log_ratio_tendsto_zero).add hd
  simp only [mul_zero, zero_add, add_zero] at h
  apply h.congr'
  filter_upwards [] with n
  have hy : (primeWindow n : ℝ) ≠ 0 := by exact_mod_cast (by have := primeWindow_ge_two n; omega : primeWindow n ≠ 0)
  simp only [primeLoss, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [Real.log_mul (mul_ne_zero (by norm_num) hy) (by positivity),
    Real.log_mul (by norm_num : (32 : ℝ) ≠ 0) hy, Real.log_pow]
  simp only [add_div, Pi.inv_apply]
  ring
end ThreeSum.Scales
