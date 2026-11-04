-- Prove2me | solution 1 for ThreeSum.HierarchyScales.allQueryTerms_eventually_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:37:01.376509+00:00
-- url     : https://prove2.me/submissions/bd97d793-558d-4b65-b35f-2c72c369a54f

import Definitions.Def_Submission_ThreeSum_CostLedger
import Definitions.Def_Submission_ThreeSum_HierarchyScales
import Theorems.Thm_ThreeSum_HierarchyScales_allQueryTerms_envelope
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
    ∀ᶠ n : ℕ in atTop, (allQueryTerms n : ℝ) ≤
      (n : ℝ) ^ ((entropyRatio * (1 + boxSaving - 2 * bandShift)) / 5 + d) := by
  have he := eventually_real_le_rpow_of_log_rate
    (hierarchyEnvelope_log_rate (entropyRatio * (1 + boxSaving - 2 * bandShift))
      (9 * entropyRatio * Real.log 2)) hd
  filter_upwards [he, TrimScales.mu_tendsto_atTop.eventually (eventually_ge_atTop 1)] with n hn hmu
  exact (allQueryTerms_envelope (by omega : 0 < mu n)).trans hn
end ThreeSum.HierarchyScales
