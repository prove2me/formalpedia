-- Prove2me | solution 1 for ThreeSum.MassScales.falseMajorant_eventually_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:55:35.486205+00:00
-- url     : https://prove2.me/submissions/5e79c837-fe17-413d-818d-105b75bfb65a

import Definitions.Def_Submission_ThreeSum_HierarchyScales
import Definitions.Def_Submission_ThreeSum_MassScales
import Theorems.Thm_ThreeSum_MassScales_falseMajorant_log_rate
import Theorems.Thm_ThreeSum_HierarchyScales_eventually_real_le_rpow_of_log_rate


set_option autoImplicit false
open ThreeSum ThreeSum.MassScales
open Filter Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.TrimScales
  ThreeSum.BandScales ThreeSum.CostLedger ThreeSum.HierarchyScales
open scoped Topology
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace ThreeSum.MassScales
theorem _root_.solution (k : ℕ) {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, falseMajorant k n ≤ (n : ℝ) ^ (2 - (1 / 2 - bandShift) / 5 + d) :=
  eventually_real_le_rpow_of_log_rate (falseMajorant_log_rate k) hd
end ThreeSum.MassScales
