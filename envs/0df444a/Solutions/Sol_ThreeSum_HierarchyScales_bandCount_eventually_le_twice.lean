-- Prove2me | solution 1 for ThreeSum.HierarchyScales.bandCount_eventually_le_twice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:37:16.464404+00:00
-- url     : https://prove2.me/submissions/bda792cd-c35c-4218-9fbf-5a81d44f3d91

import Definitions.Def_Submission_ThreeSum_CostLedger
import Definitions.Def_Submission_ThreeSum_HierarchyScales
import Theorems.Thm_ThreeSum_HierarchyScales_unroundedBandCount_eventually_ge_one
import Theorems.Thm_ThreeSum_BandScales_bandSize_pos
import Theorems.Thm_ThreeSum_CostLedger_bandCount_mul_bounds
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_Switch_mem_candidates
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.Switch.mem_candidates



set_option autoImplicit false
open ThreeSum ThreeSum.HierarchyScales
open Filter Set Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.Switch ThreeSum.CostLedger
open scoped Topology BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace ThreeSum.HierarchyScales
theorem _root_.solution :
    ∀ᶠ n : ℕ in atTop, (bandCount n : ℝ) ≤ 2 * unroundedBandCount n := by
  filter_upwards [unroundedBandCount_eventually_ge_one] with n hn
  have hb : (0 : ℝ) < BandScales.bandSize n := by exact_mod_cast BandScales.bandSize_pos n
  have hu : (BandScales.bandSize n : ℝ) * bandCount n < (n : ℝ) + BandScales.bandSize n :=
    by exact_mod_cast (bandCount_mul_bounds n).2
  have hsmall : (bandCount n : ℝ) < unroundedBandCount n + 1 := by
    rw [unroundedBandCount]
    have hid : (n : ℝ) / BandScales.bandSize n + 1 =
      ((n : ℝ) + BandScales.bandSize n) / BandScales.bandSize n := by field_simp
    rw [hid, lt_div_iff₀ hb]
    simpa only [mul_comm] using hu
  linarith
end ThreeSum.HierarchyScales
