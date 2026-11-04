-- Prove2me | solution 1 for ThreeSum.StageBounds.boxes_powerBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:46:07.045364+00:00
-- url     : https://prove2.me/submissions/c91e9f88-f754-47fd-82ba-7e867500c813

import Definitions.Def_Submission_ThreeSum_MassScales
import Definitions.Def_Submission_ThreeSum_StageBounds
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_of_rate
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_const
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_mul
import Theorems.Thm_ThreeSum_HierarchyScales_allPrefixBoxes_eventually_le
import Definitions.Def_WeightedCache3SUM_Alias_79670fd38525811b
import Theorems.Thm_ThreeSum_MassScales_nat_log_rate_pow
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
theorem _root_.solution : PowerBound boxCount (2 - epsilon * boxSaving) := by
  have hB := PowerBound.of_rate (nat_log_rate_pow bandCount_log_rate 2)
  have hQ : PowerBound allPrefixBoxes ((2 * E + 2 * bandShift - boxSaving) / 5) :=
    fun _ hd => allPrefixBoxes_eventually_le hd
  have hh := (((PowerBound.const 3).mul hB).mul (PowerBound.of_rate scheduleCount_log_rate)).mul hQ
  have heq : ((0 : ℝ) + 2 * (1 - (E + bandShift) / 5) + 0) +
      (2 * E + 2 * bandShift - boxSaving) / 5 = 2 - epsilon * boxSaving := by unfold epsilon; ring
  norm_num only [Nat.cast_ofNat] at hh
  rw [heq] at hh
  exact hh
end ThreeSum.StageBounds
