-- Prove2me | solution 1 for ThreeSum.ArithmeticStageBounds.window_powerBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:22:21.290019+00:00
-- url     : https://prove2.me/submissions/9de1978e-09ce-449c-92e1-91fa60b577e9

import Definitions.Def_Submission_ThreeSum_ModuloCosts
import Definitions.Def_Submission_ThreeSum_BudgetTime
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Theorems.Thm_ThreeSum_Scales_primeWindow_log_ratio_tendsto_zero
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_of_rate


set_option autoImplicit false
open ThreeSum ThreeSum.ArithmeticStageBounds
open Filter Real Parameters Scales BandScales CostLedger HierarchyScales
  MassScales StageBounds UniformStageBounds ModuloCosts
open scoped Topology
set_option maxHeartbeats 1000000
noncomputable section
namespace ThreeSum.ArithmeticStageBounds
theorem _root_.solution : PowerBound primeWindow 0 :=
  PowerBound.of_rate primeWindow_log_ratio_tendsto_zero
end ThreeSum.ArithmeticStageBounds
