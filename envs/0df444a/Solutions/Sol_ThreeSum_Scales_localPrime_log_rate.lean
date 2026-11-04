-- Prove2me | solution 1 for ThreeSum.Scales.localPrime_log_rate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:30:30.318648+00:00
-- url     : https://prove2.me/submissions/3a3feace-9e8a-4171-8fc4-7c5249f2c663

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
import Theorems.Thm_ThreeSum_Scales_localThreshold_log_rate
import Theorems.Thm_ThreeSum_Scales_localPrime_log_interval
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
    Tendsto (fun h : ℕ => Real.log (LocalCoverBounds.localPrime h : ℝ) /
      ((2 * h : ℝ) * Real.log 2)) atTop (𝓝 (Parameters.E + 1 / 2)) := by
  have hmain := localThreshold_log_rate.div_const 2
  have hmain' : Tendsto (fun h : ℕ =>
      Real.log (LocalCoverBounds.localThreshold h : ℝ) / ((2 * h : ℝ) * Real.log 2) / 2)
      atTop (𝓝 (Parameters.E + 1 / 2)) := by
    convert hmain using 1 <;> ring
  have herr : Tendsto (fun h : ℕ => Real.log 16 / ((4 * h : ℝ) * Real.log 2))
      atTop (𝓝 0) := by
    have hi := (tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      hi.const_mul (Real.log 16 / (4 * Real.log 2))
  have hupper := hmain'.add herr
  simp only [add_zero] at hupper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hmain' hupper
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with h hh
    have hp : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
    have hden : 0 < (2 * h : ℝ) * Real.log 2 := by positivity
    have hi := (localPrime_log_interval h).1
    apply (le_div_iff₀ hden).mpr
    have heq : (Real.log (LocalCoverBounds.localThreshold h : ℝ) /
        ((2 * h : ℝ) * Real.log 2) / 2) * ((2 * h : ℝ) * Real.log 2) =
        Real.log (LocalCoverBounds.localThreshold h : ℝ) / 2 := by field_simp
    rw [heq]
    linarith
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with h hh
    have hp : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
    have hden : 0 < (2 * h : ℝ) * Real.log 2 := by positivity
    have hi := (localPrime_log_interval h).2
    apply (div_le_iff₀ hden).mpr
    have heq : (Real.log (LocalCoverBounds.localThreshold h : ℝ) /
        ((2 * h : ℝ) * Real.log 2) / 2 + Real.log 16 / ((4 * h : ℝ) * Real.log 2)) *
        ((2 * h : ℝ) * Real.log 2) =
        (Real.log (LocalCoverBounds.localThreshold h : ℝ) + Real.log 16) / 2 := by field_simp; ring
    rw [heq]
    linarith
end ThreeSum.Scales
