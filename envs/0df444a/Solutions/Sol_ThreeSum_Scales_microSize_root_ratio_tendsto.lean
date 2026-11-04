-- Prove2me | solution 1 for ThreeSum.Scales.microSize_root_ratio_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:33:07.597646+00:00
-- url     : https://prove2.me/submissions/9f7e8f9a-2e25-48d1-967f-2a1561822710

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
import Theorems.Thm_ThreeSum_Scales_microSize_real_root_bounds
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
    Tendsto (fun m : ℕ => (microSize m : ℝ) / (m : ℝ) ^ (1 / 3 : ℝ)) atTop
      (𝓝 1) := by
  have hroot : Tendsto (fun m : ℕ => (m : ℝ) ^ (1 / 3 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp tendsto_natCast_atTop_atTop
  have hlo : Tendsto (fun m : ℕ => (1 : ℝ) - 3 * ((m : ℝ) ^ (1 / 3 : ℝ))⁻¹)
      atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (hroot.inv_tendsto_atTop.const_mul 3)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    have hp : 0 < (m : ℝ) ^ (1 / 3 : ℝ) := by positivity
    have hl := (microSize_real_root_bounds m).2
    apply (le_div_iff₀ hp).mpr
    have heq : (1 - 3 * ((m : ℝ) ^ (1 / 3 : ℝ))⁻¹) * (m : ℝ) ^ (1 / 3 : ℝ) =
        (m : ℝ) ^ (1 / 3 : ℝ) - 3 := by field_simp
    rw [heq]
    linarith
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    have hp : 0 < (m : ℝ) ^ (1 / 3 : ℝ) := by positivity
    apply (div_le_iff₀ hp).mpr
    simpa using (microSize_real_root_bounds m).1
end ThreeSum.Scales
