-- Prove2me | solution 1 for ThreeSum.LightSwitch.actual_candidates_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:04:00.969305+00:00
-- url     : https://prove2.me/submissions/2bd53026-66d9-43c8-a639-958bb9756bba

import Definitions.Def_Submission_ThreeSum_Switch
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSum_LightSwitchBounds
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_PrimeDensity_mem_candidates
import Theorems.Thm_ThreeSum_Switch_actual_depth_condition
import Theorems.Thm_ThreeSum_Switch_actual_residual_even
import Theorems.Thm_ThreeSum_Switch_candidates_nonempty
import Theorems.Thm_ThreeSum_Switch_mem_candidates
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.Switch.mem_candidates



set_option autoImplicit false
open ThreeSum ThreeSum.LightSwitch
open Light
set_option maxHeartbeats 1800000
namespace ThreeSum.LightSwitch
theorem _root_.solution {n j : ℕ} (hj : j ≤ Switch.terminalDepth n) :
    (Switch.candidates (Scales.blockCount (Scales.inputBits n)) j
      (Switch.residualSize n j)).Nonempty := by
  by_cases hz : Switch.residualSize n j=0
  · refine ⟨0,Switch.mem_candidates.mpr ⟨by omega,?_⟩⟩
    simp [Switch.accepts,Switch.cubicNumerator,hz]
  · have hJ : 0 < Scales.blockCount (Scales.inputBits n) := by
      have hh := Switch.actual_depth_condition hj
      unfold Switch.residualSize at hz
      by_contra h
      have he : Scales.blockCount (Scales.inputBits n)=0 := by omega
      simp [he] at hz
    exact Switch.candidates_nonempty hJ (Switch.actual_depth_condition hj)
      (by omega) (Switch.actual_residual_even n j)
end ThreeSum.LightSwitch
