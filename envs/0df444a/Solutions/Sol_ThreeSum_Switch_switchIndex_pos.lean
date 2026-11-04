-- Prove2me | solution 1 for ThreeSum.Switch.switchIndex_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:02:11.915569+00:00
-- url     : https://prove2.me/submissions/121d8d1d-9b78-4d4b-93fb-8c092dcabe99

import Definitions.Def_Submission_ThreeSum_BandScales
import Mathlib.Data.Finset.Max
import Definitions.Def_Submission_ThreeSum_Switch
import Theorems.Thm_ThreeSum_Switch_mem_candidates
import Theorems.Thm_ThreeSum_Switch_switchIndex_spec
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
theorem _root_.solution {J j r : ℕ} (hJ : 0 < J) (hj : 20 * j ≤ 13 * J)
    (hr : 0 < r) (heven : 2 ∣ r) : 0 < switchIndex J j r := by
  have hs := (switchIndex_spec hJ hj hr heven).2
  by_contra hn
  have hz : switchIndex J j r = 0 := by omega
  rw [hz] at hs
  have hp : 0 < (291 * J + 1000 * j) * r ^ 3 := by positivity
  simp [accepts, cubicNumerator] at hs
  omega
end ThreeSum.Switch
