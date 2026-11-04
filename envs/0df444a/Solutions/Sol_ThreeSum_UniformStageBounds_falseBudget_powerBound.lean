-- Prove2me | solution 1 for ThreeSum.UniformStageBounds.falseBudget_powerBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:58:29.797339+00:00
-- url     : https://prove2.me/submissions/0b3424d5-324e-4047-b5b8-ddae96fb571e

import Definitions.Def_Submission_ThreeSum_StageBounds
import Definitions.Def_Submission_ThreeSum_UniformStageBounds
import Theorems.Thm_ThreeSum_MassScales_falseMajorant_eventually_le
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
theorem _root_.solution (k : ℕ) : PowerBound (falseBudget k) (2 - (1 / 2 - bandShift) / 5) := by
  intro d hd
  filter_upwards [falseMajorant_eventually_le k hd] with n hn
  have hb : (falseBudget k n : ℝ) ≤ falseMajorant k n := by
    rw [falseMajorant, le_div_iff₀ (show (0 : ℝ) < radix n by exact_mod_cast radix_pos n)]
    exact_mod_cast Nat.div_mul_le_self (falseNumerator k n) (radix n)
  exact hb.trans hn
end ThreeSum.UniformStageBounds
