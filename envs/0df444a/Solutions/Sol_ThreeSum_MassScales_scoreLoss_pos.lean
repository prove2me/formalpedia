-- Prove2me | solution 1 for ThreeSum.MassScales.scoreLoss_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:17:52.820408+00:00
-- url     : https://prove2.me/submissions/71c8589c-812f-45e1-9004-cbdb08314cf9

import Definitions.Def_Submission_ThreeSum_HierarchyScales
import Definitions.Def_Submission_ThreeSum_MassScales

set_option autoImplicit false
open ThreeSum ThreeSum.MassScales
open Filter Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.TrimScales
  ThreeSum.BandScales ThreeSum.CostLedger ThreeSum.HierarchyScales
open scoped Topology
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace ThreeSum.MassScales
theorem _root_.solution (k n : ℕ) : 0 < scoreLoss k n := by
  unfold scoreLoss
  positivity
end ThreeSum.MassScales
