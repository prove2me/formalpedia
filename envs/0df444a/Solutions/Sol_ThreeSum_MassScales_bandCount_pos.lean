-- Prove2me | solution 1 for ThreeSum.MassScales.bandCount_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:22:44.430438+00:00
-- url     : https://prove2.me/submissions/eb659103-922b-4ca9-9df9-6316246f3a8b

import Definitions.Def_Submission_ThreeSum_HierarchyScales
import Definitions.Def_Submission_ThreeSum_MassScales
import Theorems.Thm_ThreeSum_CostLedger_bandCount_mul_bounds


set_option autoImplicit false
open ThreeSum ThreeSum.MassScales
open Filter Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.TrimScales
  ThreeSum.BandScales ThreeSum.CostLedger ThreeSum.HierarchyScales
open scoped Topology
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace ThreeSum.MassScales
theorem _root_.solution {n : ℕ} (hn : 0 < n) : 0 < bandCount n :=
  Nat.pos_of_mul_pos_left (hn.trans_le (bandCount_mul_bounds n).1)
end ThreeSum.MassScales
