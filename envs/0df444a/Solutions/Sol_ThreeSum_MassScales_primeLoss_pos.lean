-- Prove2me | solution 1 for ThreeSum.MassScales.primeLoss_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:17:53.893325+00:00
-- url     : https://prove2.me/submissions/c37e4afd-c3b6-42d2-967c-f2beacd38caf

import Definitions.Def_Submission_ThreeSum_HierarchyScales
import Definitions.Def_Submission_ThreeSum_MassScales
import Theorems.Thm_ThreeSum_Scales_primeWindow_ge_two


set_option autoImplicit false
open ThreeSum ThreeSum.MassScales
open Filter Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.TrimScales
  ThreeSum.BandScales ThreeSum.CostLedger ThreeSum.HierarchyScales
open scoped Topology
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace ThreeSum.MassScales
theorem _root_.solution (n : ℕ) : 0 < primeLoss radix n := by
  have hy := primeWindow_ge_two n
  unfold primeLoss
  positivity
end ThreeSum.MassScales
