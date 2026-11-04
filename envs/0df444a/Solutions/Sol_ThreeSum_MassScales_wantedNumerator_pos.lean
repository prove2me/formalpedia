-- Prove2me | solution 1 for ThreeSum.MassScales.wantedNumerator_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:47:45.575042+00:00
-- url     : https://prove2.me/submissions/16c98511-5f45-4cb7-b7ad-46f1a0219e6d

import Definitions.Def_Submission_ThreeSum_HierarchyScales
import Definitions.Def_Submission_ThreeSum_MassScales
import Theorems.Thm_ThreeSum_MassScales_scheduleCount_pos
import Theorems.Thm_ThreeSum_MassScales_bandCount_pos
import Theorems.Thm_ThreeSum_BandScales_bandSize_pos
import Theorems.Thm_ThreeSum_BandScales_typedOutputs_pos


set_option autoImplicit false
open ThreeSum ThreeSum.MassScales
open Filter Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.TrimScales
  ThreeSum.BandScales ThreeSum.CostLedger ThreeSum.HierarchyScales
open scoped Topology
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace ThreeSum.MassScales
theorem _root_.solution {n : ℕ} (hn : 0 < n) : 0 < wantedNumerator n := by
  have hS := scheduleCount_pos n
  have hM := typedOutputs_pos n
  have hB := bandCount_pos hn
  have hb := bandSize_pos n
  exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by norm_num) hS) hM)
    (Nat.pow_pos hB)) hb
end ThreeSum.MassScales
