-- Prove2me | solution 1 for ThreeSum.BandScales.bandRoot_log_rate_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:28:59.82838+00:00
-- url     : https://prove2.me/submissions/56905562-21d7-462d-aa93-ff8b9a275c41

import Definitions.Def_Submission_ThreeSum_TrimScales
import Definitions.Def_Submission_ThreeSum_BandScales
import Theorems.Thm_ThreeSum_BandScales_bandRoot_log_interval
import Theorems.Thm_ThreeSum_Asymptotics_log_nat_tendsto_atTop
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Definitions.Def_WeightedCache3SUM_Alias_e8286cd6503d6aa9
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
    Tendsto (fun n : ℕ => Real.log (bandRoot n : ℝ) / Real.log n) atTop
      (𝓝 (Parameters.E / 5)) := by
  have hl := typedOutputs_log_ratio_tendsto.div_const 2
  have heq : 2 * Parameters.E / 5 / 2 = Parameters.E / 5 := by ring
  rw [heq] at hl
  have herr := Asymptotics.log_nat_tendsto_atTop.inv_tendsto_atTop.const_mul (Real.log 4 / 2)
  have hu := hl.add herr
  simp only [mul_zero, add_zero] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    have hp : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have hb := (bandRoot_log_interval n).1
    apply (le_div_iff₀ hp).mpr
    have he : (Real.log (typedOutputs n : ℝ) / Real.log n / 2) * Real.log n =
        Real.log (typedOutputs n : ℝ) / 2 := by field_simp
    rw [he]
    linarith
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    have hp : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have hb := (bandRoot_log_interval n).2
    apply (div_le_iff₀ hp).mpr
    simp only [Pi.inv_apply]
    have he : (Real.log (typedOutputs n : ℝ) / Real.log n / 2 +
        (Real.log 4 / 2) * (Real.log n)⁻¹) * Real.log n =
        (Real.log (typedOutputs n : ℝ) + Real.log 4) / 2 := by field_simp
    rw [he]
    linarith
end ThreeSum.BandScales
