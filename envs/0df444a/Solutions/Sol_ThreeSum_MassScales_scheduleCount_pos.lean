-- Prove2me | solution 1 for ThreeSum.MassScales.scheduleCount_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:14:57.977209+00:00
-- url     : https://prove2.me/submissions/a4ab96ef-488f-4339-8ed9-851144e3c145

import Definitions.Def_Submission_ThreeSum_HierarchyScales
import Definitions.Def_Submission_ThreeSum_MassScales
import Theorems.Thm_ThreeSum_TrimScales_localLength_pos


set_option autoImplicit false
open ThreeSum ThreeSum.MassScales
open Filter Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.TrimScales
  ThreeSum.BandScales ThreeSum.CostLedger ThreeSum.HierarchyScales
open scoped Topology
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace ThreeSum.MassScales
theorem _root_.solution (n : ℕ) : 0 < scheduleCount n :=
  Nat.pow_pos (localLength_pos _)
end ThreeSum.MassScales
