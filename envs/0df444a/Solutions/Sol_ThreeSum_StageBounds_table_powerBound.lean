-- Prove2me | solution 1 for ThreeSum.StageBounds.table_powerBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:32:21.594774+00:00
-- url     : https://prove2.me/submissions/b64f9b85-acb5-43c8-9e37-4a500cefc5ae

import Definitions.Def_Submission_ThreeSum_MassScales
import Definitions.Def_Submission_ThreeSum_StageBounds
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_of_rate
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_mul
import Definitions.Def_WeightedCache3SUM_Alias_612fa2b177f14593
import Theorems.Thm_ThreeSum_TrimScales_scheduleCount_log_rate


set_option autoImplicit false
open ThreeSum ThreeSum.StageBounds
open Filter Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.TrimScales
  ThreeSum.BandScales ThreeSum.Switch ThreeSum.CostLedger ThreeSum.HierarchyScales
  ThreeSum.MassScales
open scoped Topology
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace ThreeSum.StageBounds
theorem _root_.solution : PowerBound tableCount (2 * epsilon * E) := by
  have hh := (PowerBound.of_rate scheduleCount_log_rate).mul
    (PowerBound.of_rate fullOutputs_log_rate)
  have heq : (0 : ℝ) + 2 * E / 5 = 2 * epsilon * E := by unfold epsilon; ring
  rw [heq] at hh
  exact hh
end ThreeSum.StageBounds
