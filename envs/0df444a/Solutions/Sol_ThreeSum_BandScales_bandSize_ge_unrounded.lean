-- Prove2me | solution 1 for ThreeSum.BandScales.bandSize_ge_unrounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:45:31.608537+00:00
-- url     : https://prove2.me/submissions/5cd6db42-158d-43ed-8eee-d8365e2709d4

import Definitions.Def_Submission_ThreeSum_TrimScales
import Definitions.Def_Submission_ThreeSum_BandScales
import Theorems.Thm_ThreeSum_BandScales_bandDivisor_pos
import Theorems.Thm_ThreeSum_BandScales_bandSize_mul_bounds
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices



set_option autoImplicit false
open ThreeSum ThreeSum.BandScales
open Filter Real ThreeSum.Scales
open scoped Topology
noncomputable section
namespace ThreeSum.BandScales
theorem _root_.solution (n : ℕ) : unroundedBand n ≤ (bandSize n : ℝ) := by
  have hD : (0 : ℝ) < bandDivisor n := by exact_mod_cast bandDivisor_pos n
  have hl : (bandRoot n : ℝ) ≤ (bandDivisor n : ℝ) * bandSize n := by
    exact_mod_cast (bandSize_mul_bounds n).1
  rw [unroundedBand, div_le_iff₀ hD]
  simpa only [mul_comm] using hl
end ThreeSum.BandScales
