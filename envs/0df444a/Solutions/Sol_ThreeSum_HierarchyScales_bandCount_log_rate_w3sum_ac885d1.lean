-- Prove2me | solution 1 for ThreeSum.HierarchyScales.bandCount_log_rate_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:41:45.818003+00:00
-- url     : https://prove2.me/submissions/7ad7baee-7290-45b2-b7c8-d60f79aa3e24

import Definitions.Def_Submission_ThreeSum_CostLedger
import Definitions.Def_Submission_ThreeSum_HierarchyScales
import Theorems.Thm_ThreeSum_HierarchyScales_unroundedBandCount_pos
import Theorems.Thm_ThreeSum_HierarchyScales_unroundedBandCount_log_rate
import Theorems.Thm_ThreeSum_HierarchyScales_bandCount_ge_unrounded
import Theorems.Thm_ThreeSum_HierarchyScales_bandCount_eventually_le_twice
import Theorems.Thm_ThreeSum_Asymptotics_log_nat_tendsto_atTop
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_Switch_mem_candidates
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.Switch.mem_candidates



set_option autoImplicit false
open ThreeSum ThreeSum.HierarchyScales
open Filter Set Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.Switch ThreeSum.CostLedger
open scoped Topology BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace ThreeSum.HierarchyScales
theorem _root_.solution :
    Tendsto (fun n : ℕ => Real.log (bandCount n : ℝ) / Real.log n) atTop
      (𝓝 (1 - (E + bandShift) / 5)) := by
  have he := Asymptotics.log_nat_tendsto_atTop.inv_tendsto_atTop.const_mul (Real.log 2)
  have hh := unroundedBandCount_log_rate.add he
  simp only [mul_zero, add_zero] at hh
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' unroundedBandCount_log_rate hh
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    exact div_le_div_of_nonneg_right
      (Real.log_le_log (unroundedBandCount_pos (by omega)) (bandCount_ge_unrounded n))
      (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n)))
  · filter_upwards [bandCount_eventually_le_twice, eventually_ge_atTop (2 : ℕ)] with n hn hge
    have hp : (0 : ℝ) < bandCount n :=
      lt_of_lt_of_le (unroundedBandCount_pos (by omega)) (bandCount_ge_unrounded n)
    have hlog := Real.log_le_log hp hn
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (unroundedBandCount_pos (by omega : 0 < n)).ne'] at hlog
    have hd := div_le_div_of_nonneg_right hlog
      (show 0 ≤ Real.log (n : ℝ) from Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n)))
    simpa only [add_div, Pi.inv_apply, div_eq_mul_inv, add_mul, add_comm] using hd
end ThreeSum.HierarchyScales
