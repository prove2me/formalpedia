-- Prove2me | solution 1 for ThreeSum.Scales.scoreLoss_log_ratio_tendsto_zero_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:49:01.679453+00:00
-- url     : https://prove2.me/submissions/1ee7f6fc-0dc8-4d56-ba81-6238325f345a

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
import Theorems.Thm_ThreeSum_Scales_radix_log_ratio_tendsto
import Theorems.Thm_ThreeSum_Scales_radix_eventually_ge_four
import Theorems.Thm_ThreeSum_Scales_primeDepth_log_bound
import Theorems.Thm_ThreeSum_Scales_scoreBase_log_over_primeBase_tendsto_zero
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
theorem _root_.solution (k : ℕ) :
    Tendsto (fun n : ℕ => Real.log (scoreLoss k n : ℝ) / Real.log n) atTop (𝓝 0) := by
  have hu := radix_log_ratio_tendsto.mul (scoreBase_log_over_primeBase_tendsto_zero k)
  simp only [mul_zero] at hu
  apply squeeze_zero' _ _ hu
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact div_nonneg (Real.log_natCast_nonneg _) (Real.log_nonneg (by exact_mod_cast hn))
  · filter_upwards [radix_eventually_ge_four, eventually_ge_atTop (2 : ℕ)] with n hR hn
    have hy := primeWindow_ge_two n
    have hb : 0 < Real.log (4 * primeWindow n : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < 4 * primeWindow n))
    have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have hs : 0 ≤ Real.log (16 * ((k : ℝ) + 2) * (inputBits n + 1)) := by
      apply Real.log_nonneg
      have hk := Nat.cast_nonneg (α := ℝ) k
      have hm := Nat.cast_nonneg (α := ℝ) (inputBits n)
      nlinarith
    have hd := (le_div_iff₀ hb).mpr (primeDepth_log_bound hR)
    have hmul := mul_le_mul_of_nonneg_right hd hs
    have hdiv := div_le_div_of_nonneg_right hmul hlog.le
    simp only [scoreLoss, Nat.cast_pow, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat,
      Nat.cast_one, Real.log_pow]
    apply le_of_le_of_eq hdiv
    ring
end ThreeSum.Scales
