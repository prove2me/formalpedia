-- Prove2me | solution 1 for ThreeSum.UniformStageBounds.wantedBudget_powerBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:55:44.420379+00:00
-- url     : https://prove2.me/submissions/2b73c92a-38fe-4d67-817d-8907bed44d78

import Definitions.Def_Submission_ThreeSum_StageBounds
import Definitions.Def_Submission_ThreeSum_UniformStageBounds
import Theorems.Thm_ThreeSum_UniformStageBounds_wantedBudget_mul_le
import Theorems.Thm_ThreeSum_StageBounds_wanted_powerBound


set_option autoImplicit false
open ThreeSum ThreeSum.UniformStageBounds
open Filter Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.TrimScales
  ThreeSum.BandScales ThreeSum.Switch ThreeSum.CostLedger ThreeSum.HierarchyScales
  ThreeSum.MassScales ThreeSum.StageBounds
open scoped Topology
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace ThreeSum.UniformStageBounds
theorem _root_.solution : PowerBound wantedBudget (2 - (1 / 2 + bandShift) / 5) :=
  wanted_powerBound (Filter.Eventually.of_forall wantedBudget_mul_le)
end ThreeSum.UniformStageBounds
