-- Prove2me | solution 1 for ThreeSum.Switch.actual_switch_certified_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:23:30.744741+00:00
-- url     : https://prove2.me/submissions/b2765a6a-7d90-406f-977d-daafff5eb429

import Definitions.Def_Submission_ThreeSum_BandScales
import Mathlib.Data.Finset.Max
import Definitions.Def_Submission_ThreeSum_Switch
import Theorems.Thm_ThreeSum_Switch_mem_candidates
import Theorems.Thm_ThreeSum_Switch_depth_fraction
import Theorems.Thm_ThreeSum_Switch_switch_ratio_mem
import Theorems.Thm_ThreeSum_Switch_phi_enclosure
import Theorems.Thm_ThreeSum_Switch_actual_totalSize
import Theorems.Thm_ThreeSum_Switch_actual_residual_even
import Theorems.Thm_ThreeSum_Switch_actual_depth_condition
import Theorems.Thm_ThreeSum_Switch_actual_residual_pos
import Theorems.Thm_ThreeSum_Switch_residual_real_identity
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_Parameters_switch_box_bound
import Definitions.Def_WeightedCache3SUM_Alias_3298d8ed0aa9123b
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
    let a : ℝ := (j : ℝ) / blockCount (inputBits n)
    let t : ℝ := (actualSwitch n j : ℝ) / residualSize n j
    t ∈ Icc (0 : ℝ) (1 / 2) ∧
      boxSaving ≤ 2 * bandShift - a + (1 - a) * gamma t ∧
      (1 - a) * entropy t <
        entropyRatio * (1 + boxSaving - 2 * bandShift) + 9 * entropyRatio / mu n := by
  dsimp only
  have hm := hmu
  rw [actual_totalSize] at hm
  have hp := And.intro (Nat.pos_of_mul_pos_right hm) (Nat.pos_of_mul_pos_left hm)
  have hdepth := actual_depth_condition hj
  have hr := actual_residual_pos hmu hj
  have he := actual_residual_even n j
  have ha := depth_fraction hp.1 hdepth
  have ht := switch_ratio_mem hp.1 hdepth hr he
  have hf := phi_enclosure hp.1 hdepth hr he
  change ((switchIndex _ _ _ : ℝ) / _) ∈ _ ∧ _
  refine ⟨ht, switch_box_bound ha ht hf.1, ?_⟩
  apply switch_entropy_bound ha ht (by exact_mod_cast hmu)
  rw [← residual_real_identity hmu hj]
  exact hf.2
end ThreeSum.Switch
