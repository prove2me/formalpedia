-- Prove2me | solution 1 for ThreeSum.UniformStageBounds.budget_initial_powerBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:58:33.903197+00:00
-- url     : https://prove2.me/submissions/151e7903-289e-4331-90be-d6db724e8d75

import Definitions.Def_Submission_ThreeSum_StageBounds
import Definitions.Def_Submission_ThreeSum_UniformStageBounds
import Theorems.Thm_ThreeSum_UniformStageBounds_wantedBudget_mul_le
import Theorems.Thm_ThreeSum_StageBounds_initial_powerBound


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
theorem _root_.solution :
    PowerBound (initialCount wantedBudget)
      (2 - epsilon * (1 / 2 + bandShift - entropy initialTheta)) :=
  initial_powerBound (Filter.Eventually.of_forall wantedBudget_mul_le)
end ThreeSum.UniformStageBounds
