-- Prove2me | solution 1 for ThreeSum.Switch.residual_real_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:10:33.872869+00:00
-- url     : https://prove2.me/submissions/c0479994-f354-4ece-81a2-dcbe8ed7e743

import Definitions.Def_Submission_ThreeSum_BandScales
import Mathlib.Data.Finset.Max
import Definitions.Def_Submission_ThreeSum_Switch
import Theorems.Thm_ThreeSum_Switch_mem_candidates
import Theorems.Thm_ThreeSum_Switch_depth_lt
import Theorems.Thm_ThreeSum_Switch_actual_totalSize
import Theorems.Thm_ThreeSum_Switch_actual_depth_condition
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_PrimeDensity_mem_candidates
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices


attribute [local simp] ThreeSum.Switch.mem_candidates

set_option autoImplicit false
open ThreeSum ThreeSum.Switch
open Set ThreeSum.Parameters ThreeSum.Scales
set_option maxHeartbeats 0
noncomputable section
namespace ThreeSum.Switch
theorem _root_.solution {n j : ℕ} (hmu : 0 < mu n)
    (hj : j ≤ terminalDepth n) :
    (residualSize n j : ℝ) =
      (1 - (j : ℝ) / blockCount (inputBits n)) * mu n := by
  have hm := hmu
  rw [actual_totalSize] at hm
  have hp := And.intro (Nat.pos_of_mul_pos_right hm) (Nat.pos_of_mul_pos_left hm)
  have hlt := depth_lt hp.1 (actual_depth_condition hj)
  have hJ : (blockCount (inputBits n) : ℝ) ≠ 0 := by exact_mod_cast hp.1.ne'
  simp only [residualSize, actual_totalSize, Nat.cast_mul, Nat.cast_sub hlt.le]
  field_simp
  <;> ring
end ThreeSum.Switch
