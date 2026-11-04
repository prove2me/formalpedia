-- Prove2me | solution 1 for ThreeSum.Switch.predecessor_rejected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:06:55.826198+00:00
-- url     : https://prove2.me/submissions/9dc49d42-996e-44bd-aea2-4af7c7a3c8cc

import Definitions.Def_Submission_ThreeSum_BandScales
import Mathlib.Data.Finset.Max
import Definitions.Def_Submission_ThreeSum_Switch
import Theorems.Thm_ThreeSum_Switch_mem_candidates
import Theorems.Thm_ThreeSum_Switch_switchIndex_le
import Theorems.Thm_ThreeSum_Switch_switchIndex_spec
import Theorems.Thm_ThreeSum_Switch_switchIndex_pos
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
    (hr : 0 < r) (heven : 2 ∣ r) :
    ¬ accepts J j r (switchIndex J j r - 1) := by
  have hpos := switchIndex_pos hJ hj hr heven
  have hle := (switchIndex_spec hJ hj hr heven).1
  intro ha
  have hm : switchIndex J j r - 1 ∈ candidates J j r :=
    mem_candidates.mpr ⟨by omega, ha⟩
  have hbad := switchIndex_le hm
  omega
end ThreeSum.Switch
