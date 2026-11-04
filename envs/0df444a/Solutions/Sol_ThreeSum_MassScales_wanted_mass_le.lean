-- Prove2me | solution 1 for ThreeSum.MassScales.wanted_mass_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:47:47.870194+00:00
-- url     : https://prove2.me/submissions/48560966-33d7-495b-a3f6-230ff4243ec7

import Definitions.Def_Submission_ThreeSum_HierarchyScales
import Definitions.Def_Submission_ThreeSum_MassScales
import Theorems.Thm_ThreeSum_Scales_radix_pos


set_option autoImplicit false
open ThreeSum ThreeSum.MassScales
open Filter Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.TrimScales
  ThreeSum.BandScales ThreeSum.CostLedger ThreeSum.HierarchyScales
open scoped Topology
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace ThreeSum.MassScales
theorem _root_.solution {n W : ℕ} (hW : W * radix n ≤ wantedNumerator n) :
    (W : ℝ) ≤ wantedMajorant n := by
  rw [wantedMajorant, le_div_iff₀ (show (0 : ℝ) < radix n by exact_mod_cast radix_pos n)]
  exact_mod_cast hW
end ThreeSum.MassScales
