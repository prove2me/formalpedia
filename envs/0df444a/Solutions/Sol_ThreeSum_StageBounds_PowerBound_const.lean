-- Prove2me | solution 1 for ThreeSum.StageBounds.PowerBound.const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:22:05.409857+00:00
-- url     : https://prove2.me/submissions/a28f0198-1b38-43a5-aa09-955fa664e001

import Definitions.Def_Submission_ThreeSum_MassScales
import Definitions.Def_Submission_ThreeSum_StageBounds
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_of_rate
import Theorems.Thm_ThreeSum_MassScales_nat_log_rate_const


set_option autoImplicit false
open ThreeSum ThreeSum.StageBounds
open Filter Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.TrimScales
  ThreeSum.BandScales ThreeSum.Switch ThreeSum.CostLedger ThreeSum.HierarchyScales
  ThreeSum.MassScales
open scoped Topology
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
open ThreeSum.StageBounds.PowerBound
namespace ThreeSum.StageBounds.PowerBound
theorem _root_.solution (c : ℕ) : PowerBound (fun _ => c) 0 := of_rate (nat_log_rate_const c)
end ThreeSum.StageBounds.PowerBound
