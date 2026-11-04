-- Prove2me | solution 1 for ThreeSum.HierarchyScales.initial_query_eventually_le_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:31:38.201752+00:00
-- url     : https://prove2.me/submissions/811078b9-1ff1-474c-85e2-8bac1f636068

import Definitions.Def_Submission_ThreeSum_CostLedger
import Definitions.Def_Submission_ThreeSum_HierarchyScales
import Theorems.Thm_ThreeSum_HierarchyScales_initial_query_log_bound
import Theorems.Thm_ThreeSum_HierarchyScales_initial_entropy_tendsto
import Theorems.Thm_ThreeSum_Scales_mu_log_ratio_tendsto
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
    ∀ᶠ n : ℕ in atTop, (queryTerms n 0 : ℝ) ≤
      (n : ℝ) ^ (entropy initialTheta / 5 + d) := by
  have hm := mu_log_ratio_tendsto.const_mul (Real.log 2)
  have hid : Real.log 2 * (1 / (5 * Real.log 2)) = (1 / 5 : ℝ) := by field_simp
  rw [hid] at hm
  have hh := hm.mul initial_entropy_tendsto
  have hrate : Tendsto
      (fun n : ℕ => ((mu n : ℝ) * Real.log 2 * entropy (initialTheta + 1 / (mu n : ℝ))) /
        Real.log n) atTop (𝓝 (entropy initialTheta / 5)) := by
    convert hh using 1
    · funext n
      ring
    · ring
  have hs := hrate.eventually (gt_mem_nhds (by linarith : entropy initialTheta / 5 < entropy initialTheta / 5 + d))
  filter_upwards [hs, TrimScales.mu_tendsto_atTop.eventually (eventually_ge_atTop 50),
    eventually_ge_atTop (2 : ℕ)] with n hn hmu hge
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hb := initial_query_log_bound hmu
  exact Real.le_rpow_of_log_le (by exact_mod_cast (by omega : 0 < n))
    (hb.trans ((div_lt_iff₀ hlog).mp hn).le)
end ThreeSum.HierarchyScales
