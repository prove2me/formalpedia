-- Prove2me | solution 1 for ThreeSum.UniformStageBounds.false_le_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:48:37.679231+00:00
-- url     : https://prove2.me/submissions/9e109252-23ae-41a3-b7f4-3a29b39120f4

import Definitions.Def_Submission_ThreeSum_StageBounds
import Definitions.Def_Submission_ThreeSum_UniformStageBounds
import Theorems.Thm_ThreeSum_MassScales_false_mass_le
import Theorems.Thm_ThreeSum_Scales_radix_pos


set_option autoImplicit false
open ThreeSum ThreeSum.UniformStageBounds
open Filter Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.TrimScales
  ThreeSum.BandScales ThreeSum.Switch ThreeSum.CostLedger ThreeSum.HierarchyScales
  ThreeSum.MassScales ThreeSum.StageBounds
open scoped Topology
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace ThreeSum.UniformStageBounds
theorem _root_.solution {n k P H H1 : ℕ}
    (hscore : P * H ≤ scoreLoss k n * H1)
    (hinit : H1 ≤ candidateCount n * rawTripleBound n)
    (hmod : radix n ≤ primeLoss radix n * P) : H ≤ falseBudget k n := by
  have hr := false_mass_le hscore hinit hmod
  rw [falseMajorant, le_div_iff₀ (show (0 : ℝ) < radix n by exact_mod_cast radix_pos n)] at hr
  apply (Nat.le_div_iff_mul_le (radix_pos n)).mpr
  exact_mod_cast hr
end ThreeSum.UniformStageBounds
