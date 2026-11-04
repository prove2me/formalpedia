-- Prove2me | solution 1 for ThreeSum.Switch.switchIndex_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:10:57.135673+00:00
-- url     : https://prove2.me/submissions/c447d9b3-6a74-43e2-9e13-4cfd06def2e6

import Definitions.Def_Submission_ThreeSum_BandScales
import Mathlib.Data.Finset.Max
import Definitions.Def_Submission_ThreeSum_Switch
import Theorems.Thm_ThreeSum_Switch_mem_candidates
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
namespace ThreeSum.Switch
theorem _root_.solution {J j r q : ℕ} (hq : q ∈ candidates J j r) :
    switchIndex J j r ≤ q := by
  have h : (candidates J j r).Nonempty := ⟨q, hq⟩
  simp only [switchIndex, dif_pos h]
  exact Finset.min'_le _ _ hq
end ThreeSum.Switch
