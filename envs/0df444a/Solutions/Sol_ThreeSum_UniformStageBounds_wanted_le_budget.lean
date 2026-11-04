-- Prove2me | solution 1 for ThreeSum.UniformStageBounds.wanted_le_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:52:30.195191+00:00
-- url     : https://prove2.me/submissions/b64f01d9-10ec-4fbc-93de-b81119b58cc0

import Definitions.Def_Submission_ThreeSum_StageBounds
import Definitions.Def_Submission_ThreeSum_UniformStageBounds
import Theorems.Thm_ThreeSum_Scales_radix_pos


set_option autoImplicit false
open ThreeSum ThreeSum.UniformStageBounds
open Filter Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.TrimScales
  ThreeSum.BandScales ThreeSum.Switch ThreeSum.CostLedger ThreeSum.HierarchyScales
  ThreeSum.MassScales ThreeSum.StageBounds
open scoped Topology
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace ThreeSum.UniformStageBounds
theorem _root_.solution {n W : ℕ} (hW : W * radix n ≤ wantedNumerator n) :
    W ≤ wantedBudget n := (Nat.le_div_iff_mul_le (radix_pos n)).mpr hW
end ThreeSum.UniformStageBounds
