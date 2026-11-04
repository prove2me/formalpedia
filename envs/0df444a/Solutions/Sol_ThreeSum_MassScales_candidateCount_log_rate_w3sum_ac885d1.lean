-- Prove2me | solution 1 for ThreeSum.MassScales.candidateCount_log_rate_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:23:31.935226+00:00
-- url     : https://prove2.me/submissions/e529cd60-1c6c-41aa-bcd2-5d8677559435

import Definitions.Def_Submission_ThreeSum_HierarchyScales
import Definitions.Def_Submission_ThreeSum_MassScales
import Theorems.Thm_ThreeSum_MassScales_candidateCount_eventually_pos
import Theorems.Thm_ThreeSum_MassScales_nat_log_rate_const
import Theorems.Thm_ThreeSum_MassScales_nat_log_rate_mul
import Theorems.Thm_ThreeSum_MassScales_candidateCount_le_window
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_Scales_primeWindow_ge_two
import Theorems.Thm_ThreeSum_Scales_primeWindow_log_ratio_tendsto_zero
import Theorems.Thm_ThreeSum_Switch_mem_candidates
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.Switch.mem_candidates



set_option autoImplicit false
open ThreeSum ThreeSum.MassScales
open Filter Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.TrimScales
  ThreeSum.BandScales ThreeSum.CostLedger ThreeSum.HierarchyScales
open scoped Topology
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace ThreeSum.MassScales
theorem _root_.solution :
    Tendsto (fun n : ℕ => Real.log (candidateCount n : ℝ) / Real.log n) atTop (𝓝 0) := by
  have hu := nat_log_rate_mul (nat_log_rate_const 4) primeWindow_log_ratio_tendsto_zero (by
    filter_upwards [] with n
    have hy := primeWindow_ge_two n
    omega)
  simp only [zero_add] at hu
  apply squeeze_zero' _ _ hu
  · filter_upwards [candidateCount_eventually_pos, eventually_ge_atTop (1 : ℕ)] with n hC hn
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hC))
      (Real.log_nonneg (by exact_mod_cast hn))
  · filter_upwards [candidateCount_eventually_pos, eventually_ge_atTop (1 : ℕ)] with n hC hn
    exact div_le_div_of_nonneg_right
      (Real.log_le_log (by exact_mod_cast hC) (by exact_mod_cast candidateCount_le_window n))
      (Real.log_nonneg (by exact_mod_cast hn))
end ThreeSum.MassScales
