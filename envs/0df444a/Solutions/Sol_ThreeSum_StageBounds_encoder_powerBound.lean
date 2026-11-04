-- Prove2me | solution 1 for ThreeSum.StageBounds.encoder_powerBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:46:10.736279+00:00
-- url     : https://prove2.me/submissions/74b9dd66-90f8-4892-89c8-523880752575

import Definitions.Def_Submission_ThreeSum_MassScales
import Definitions.Def_Submission_ThreeSum_StageBounds
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_of_rate
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_const
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_mul
import Definitions.Def_WeightedCache3SUM_Alias_79670fd38525811b
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
theorem _root_.solution : PowerBound encoderCount (1 + epsilon * (E - bandShift)) := by
  have hh := (((PowerBound.const 2).mul (PowerBound.of_rate bandCount_log_rate)).mul
    (PowerBound.of_rate scheduleCount_log_rate)).mul (PowerBound.of_rate fullOutputs_log_rate)
  have heq : ((0 : ℝ) + (1 - (E + bandShift) / 5) + 0) + 2 * E / 5 =
      1 + epsilon * (E - bandShift) := by unfold epsilon; ring
  rw [heq] at hh
  exact hh
end ThreeSum.StageBounds
