-- Prove2me | solution 1 for ThreeSum.Scales.totalSize_ratio_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:03:44.259034+00:00
-- url     : https://prove2.me/submissions/f7693979-3798-48c3-ae4b-2353205f9bdb

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
import Theorems.Thm_ThreeSum_Scales_totalSize_upper
import Theorems.Thm_ThreeSum_Scales_microSize_tendsto_atTop
import Theorems.Thm_ThreeSum_Scales_microSize_ratio_tendsto_zero
import Theorems.Thm_ThreeSum_Scales_totalSize_real_bounds
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
    Tendsto (fun m : ℕ => (totalSize m : ℝ) / m) atTop (𝓝 (1 / 5)) := by
  have hlo : Tendsto (fun m : ℕ => (1 / 5 : ℝ) - 20 * ((microSize m : ℝ) / m))
      atTop (𝓝 (1 / 5)) := by
    simpa using tendsto_const_nhds.sub (microSize_ratio_tendsto_zero.const_mul 20)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
  · filter_upwards [microSize_tendsto_atTop.eventually (eventually_ge_atTop 1),
      eventually_ge_atTop (1 : ℕ)] with m hm hmpos
    have hmp : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    have hl := (totalSize_real_bounds (by omega : 0 < microSize m)).1.le
    apply (le_div_iff₀ hmp).mpr
    calc
      _ = (m : ℝ) / 5 - 20 * microSize m := by field_simp
      _ ≤ _ := hl
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    have hmp : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    apply (div_le_iff₀ hmp).mpr
    have hu : (5 : ℝ) * totalSize m ≤ (m : ℝ) := by
      exact_mod_cast totalSize_upper m
    linarith
end ThreeSum.Scales
