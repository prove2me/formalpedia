-- Prove2me | solution 1 for ThreeSum.ArithmeticStageBounds.maxMod_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:02:04.50974+00:00
-- url     : https://prove2.me/submissions/aa40ef05-c240-442d-ba5d-2cbe41e50479

import Definitions.Def_Submission_ThreeSum_ModuloCosts
import Definitions.Def_Submission_ThreeSum_BudgetTime
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Theorems.Thm_ThreeSum_Scales_primeWindow_ge_two
import Theorems.Thm_ThreeSum_Scales_radix_pos


set_option autoImplicit false
open ThreeSum ThreeSum.ArithmeticStageBounds
open Filter Real Parameters Scales BandScales CostLedger HierarchyScales
  MassScales StageBounds UniformStageBounds ModuloCosts
open scoped Topology
set_option maxHeartbeats 1000000
namespace ThreeSum.ArithmeticStageBounds
theorem _root_.solution (n : ℕ) : 0 < maxMod n := by
  unfold maxMod
  exact Nat.mul_pos (radix_pos n) (Nat.pow_pos (by have := primeWindow_ge_two n; omega))
end ThreeSum.ArithmeticStageBounds
