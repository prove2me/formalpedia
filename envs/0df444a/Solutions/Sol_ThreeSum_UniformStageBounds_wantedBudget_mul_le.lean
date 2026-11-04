-- Prove2me | solution 1 for ThreeSum.UniformStageBounds.wantedBudget_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:21:51.382572+00:00
-- url     : https://prove2.me/submissions/f623e623-0ba8-4369-bb78-07b1ef346e01

import Definitions.Def_Submission_ThreeSum_StageBounds
import Definitions.Def_Submission_ThreeSum_UniformStageBounds

set_option autoImplicit false
open ThreeSum ThreeSum.UniformStageBounds
open Filter Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.TrimScales
  ThreeSum.BandScales ThreeSum.Switch ThreeSum.CostLedger ThreeSum.HierarchyScales
  ThreeSum.MassScales ThreeSum.StageBounds
open scoped Topology
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace ThreeSum.UniformStageBounds
theorem _root_.solution (n : ℕ) : wantedBudget n * radix n ≤ wantedNumerator n :=
  Nat.div_mul_le_self _ _
end ThreeSum.UniformStageBounds
