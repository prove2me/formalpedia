-- Prove2me | solution 1 for ThreeSum.BandScales.bandSize_log_rate_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:27:09.8958+00:00
-- url     : https://prove2.me/submissions/97ba802a-c534-47b4-835a-0b930f992355

import Definitions.Def_Submission_ThreeSum_TrimScales
import Definitions.Def_Submission_ThreeSum_BandScales
import Theorems.Thm_ThreeSum_BandScales_bandSize_pos
import Theorems.Thm_ThreeSum_BandScales_unroundedBand_pos
import Theorems.Thm_ThreeSum_BandScales_unroundedBand_log_rate
import Theorems.Thm_ThreeSum_BandScales_bandSize_ge_unrounded
import Theorems.Thm_ThreeSum_BandScales_bandSize_eventually_le_twice_unrounded
import Theorems.Thm_ThreeSum_Asymptotics_log_nat_tendsto_atTop
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices



set_option autoImplicit false
open ThreeSum ThreeSum.BandScales
open Filter Real ThreeSum.Scales
open scoped Topology
noncomputable section
namespace ThreeSum.BandScales
theorem _root_.solution :
    Tendsto (fun n : ℕ => Real.log (bandSize n : ℝ) / Real.log n) atTop
      (𝓝 ((Parameters.E - 1 / 20) / 5)) := by
  have herr := Asymptotics.log_nat_tendsto_atTop.inv_tendsto_atTop.const_mul (Real.log 2)
  have hu := unroundedBand_log_rate.add herr
  simp only [mul_zero, add_zero] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' unroundedBand_log_rate hu
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact div_le_div_of_nonneg_right
      (Real.log_le_log (unroundedBand_pos n) (bandSize_ge_unrounded n))
      (Real.log_nonneg (by exact_mod_cast hn))
  · filter_upwards [bandSize_eventually_le_twice_unrounded, eventually_ge_atTop (1 : ℕ)] with n hn hge
    have hpos : (0 : ℝ) < bandSize n := by exact_mod_cast bandSize_pos n
    have hlog := Real.log_le_log hpos hn
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (unroundedBand_pos n).ne'] at hlog
    have hd := div_le_div_of_nonneg_right hlog
      (show 0 ≤ Real.log (n : ℝ) from Real.log_nonneg (by exact_mod_cast hge))
    simpa only [add_div, Pi.inv_apply, div_eq_mul_inv, add_mul, add_comm] using hd
end ThreeSum.BandScales
