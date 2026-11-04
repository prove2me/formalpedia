-- Prove2me | solution 1 for ThreeSum.MassScales.rawTripleBound_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:26:46.198203+00:00
-- url     : https://prove2.me/submissions/17163789-e1ef-41f6-9f5c-4e0c684e1444

import Definitions.Def_Submission_ThreeSum_HierarchyScales
import Definitions.Def_Submission_ThreeSum_MassScales
import Theorems.Thm_ThreeSum_MassScales_bandCount_pos
import Theorems.Thm_ThreeSum_BandScales_bandSize_pos


set_option autoImplicit false
open ThreeSum ThreeSum.MassScales
open Filter Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.TrimScales
  ThreeSum.BandScales ThreeSum.CostLedger ThreeSum.HierarchyScales
open scoped Topology
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace ThreeSum.MassScales
theorem _root_.solution {n : ℕ} (hn : 0 < n) : 0 < rawTripleBound n := by
  have hB := bandCount_pos hn
  have hb := bandSize_pos n
  unfold rawTripleBound
  positivity
end ThreeSum.MassScales
