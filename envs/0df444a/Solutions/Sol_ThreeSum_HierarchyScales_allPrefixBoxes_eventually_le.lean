-- Prove2me | solution 1 for ThreeSum.HierarchyScales.allPrefixBoxes_eventually_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:37:15.264862+00:00
-- url     : https://prove2.me/submissions/5da4c184-5c2f-4321-9a45-34507fa10cb9

import Definitions.Def_Submission_ThreeSum_CostLedger
import Definitions.Def_Submission_ThreeSum_HierarchyScales
import Theorems.Thm_ThreeSum_HierarchyScales_allPrefixBoxes_envelope
import Definitions.Def_WeightedCache3SUM_Alias_28218b5ac06d5c5c
import Theorems.Thm_ThreeSum_HierarchyScales_eventually_real_le_rpow_of_log_rate
import Theorems.Thm_ThreeSum_TrimScales_mu_tendsto_atTop


set_option autoImplicit false
open ThreeSum ThreeSum.HierarchyScales
open Filter Set Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.Switch ThreeSum.CostLedger
open scoped Topology BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace ThreeSum.HierarchyScales
theorem _root_.solution {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, (allPrefixBoxes n : ℝ) ≤
      (n : ℝ) ^ ((2 * E + 2 * bandShift - boxSaving) / 5 + d) := by
  have he := eventually_real_le_rpow_of_log_rate
    (hierarchyEnvelope_log_rate (2 * E + 2 * bandShift - boxSaving) 0) hd
  filter_upwards [he, TrimScales.mu_tendsto_atTop.eventually (eventually_ge_atTop 1)] with n hn hmu
  exact (allPrefixBoxes_envelope (by omega : 0 < mu n)).trans hn
end ThreeSum.HierarchyScales
