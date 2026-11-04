-- Prove2me | solution 1 for ThreeSum.Switch.candidates_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:54:14.317845+00:00
-- url     : https://prove2.me/submissions/d79cee1d-ede7-4e7b-8e58-02b886700191

import Definitions.Def_Submission_ThreeSum_BandScales
import Mathlib.Data.Finset.Max
import Definitions.Def_Submission_ThreeSum_Switch
import Theorems.Thm_ThreeSum_Switch_mem_candidates
import Theorems.Thm_ThreeSum_Switch_depth_fraction
import Theorems.Thm_ThreeSum_Switch_depth_lt
import Theorems.Thm_ThreeSum_Switch_accepts_iff
import Theorems.Thm_ThreeSum_Switch_half_fraction
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_Parameters_phi_half
import Theorems.Thm_ThreeSum_Parameters_switchThreshold_upper
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
theorem _root_.solution {J j r : ℕ} (hJ : 0 < J) (hj : 20 * j ≤ 13 * J)
    (hr : 0 < r) (heven : 2 ∣ r) : (candidates J j r).Nonempty := by
  refine ⟨r / 2, mem_candidates.mpr ⟨le_rfl, ?_⟩⟩
  rw [accepts_iff hJ (depth_lt hJ hj) hr, half_fraction hr heven, phi_half]
  have h := switchThreshold_upper (depth_fraction hJ hj)
  linarith
end ThreeSum.Switch
