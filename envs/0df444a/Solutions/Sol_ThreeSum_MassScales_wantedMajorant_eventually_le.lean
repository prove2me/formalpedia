-- Prove2me | solution 1 for ThreeSum.MassScales.wantedMajorant_eventually_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:50:45.819358+00:00
-- url     : https://prove2.me/submissions/d781a476-02f8-4791-ad23-d27dac3df2e9

import Definitions.Def_Submission_ThreeSum_HierarchyScales
import Definitions.Def_Submission_ThreeSum_MassScales
import Theorems.Thm_ThreeSum_MassScales_wantedMajorant_log_rate
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
theorem _root_.solution {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, wantedMajorant n ≤ (n : ℝ) ^ (2 - (1 / 2 + bandShift) / 5 + d) :=
  eventually_real_le_rpow_of_log_rate wantedMajorant_log_rate hd
end ThreeSum.MassScales
