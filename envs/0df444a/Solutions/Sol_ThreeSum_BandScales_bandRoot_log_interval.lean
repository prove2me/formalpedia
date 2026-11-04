-- Prove2me | solution 1 for ThreeSum.BandScales.bandRoot_log_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:45:30.007041+00:00
-- url     : https://prove2.me/submissions/ddc59598-3665-48b9-a036-7f310bbfa7b7

import Definitions.Def_Submission_ThreeSum_TrimScales
import Definitions.Def_Submission_ThreeSum_BandScales
import Theorems.Thm_ThreeSum_BandScales_typedOutputs_pos
import Theorems.Thm_ThreeSum_BandScales_bandRoot_pos
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LocalCoverBounds_le_rootCeiling_sq
import Theorems.Thm_ThreeSum_LocalCoverBounds_rootCeiling_sq_le_four
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices



set_option autoImplicit false
open ThreeSum ThreeSum.BandScales
open Filter Real ThreeSum.Scales
open scoped Topology
noncomputable section
namespace ThreeSum.BandScales
theorem _root_.solution (n : ℕ) :
    Real.log (typedOutputs n : ℝ) ≤ 2 * Real.log (bandRoot n : ℝ) ∧
      2 * Real.log (bandRoot n : ℝ) ≤ Real.log 4 + Real.log (typedOutputs n : ℝ) := by
  have hM : (0 : ℝ) < typedOutputs n := by exact_mod_cast typedOutputs_pos n
  have hr : (0 : ℝ) < bandRoot n := by exact_mod_cast bandRoot_pos n
  have hlo : (typedOutputs n : ℝ) ≤ (bandRoot n : ℝ) ^ 2 := by
    exact_mod_cast LocalCoverBounds.le_rootCeiling_sq (typedOutputs n)
  have hup : (bandRoot n : ℝ) ^ 2 ≤ 4 * (typedOutputs n : ℝ) := by
    exact_mod_cast LocalCoverBounds.rootCeiling_sq_le_four (typedOutputs_pos n)
  constructor
  · simpa only [Real.log_pow, Nat.cast_ofNat] using Real.log_le_log hM hlo
  · simpa only [Real.log_pow, Nat.cast_ofNat,
      Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hM.ne'] using
      Real.log_le_log (by positivity : (0 : ℝ) < (bandRoot n : ℝ) ^ 2) hup
end ThreeSum.BandScales
