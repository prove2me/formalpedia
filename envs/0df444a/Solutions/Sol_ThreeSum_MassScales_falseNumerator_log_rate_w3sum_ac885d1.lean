-- Prove2me | solution 1 for ThreeSum.MassScales.falseNumerator_log_rate_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:48:24.760393+00:00
-- url     : https://prove2.me/submissions/f1db7692-29c7-447d-bdaa-6f645a35f61d

import Definitions.Def_Submission_ThreeSum_HierarchyScales
import Definitions.Def_Submission_ThreeSum_MassScales
import Theorems.Thm_ThreeSum_MassScales_rawTripleBound_pos
import Theorems.Thm_ThreeSum_MassScales_scoreLoss_pos
import Theorems.Thm_ThreeSum_MassScales_primeLoss_pos
import Theorems.Thm_ThreeSum_MassScales_candidateCount_eventually_pos
import Theorems.Thm_ThreeSum_MassScales_nat_log_rate_mul
import Definitions.Def_WeightedCache3SUM_Alias_f0985c8e07946078
import Theorems.Thm_ThreeSum_MassScales_rawTripleBound_log_rate
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Definitions.Def_WeightedCache3SUM_Alias_7d21bf991a6a3a7b
import Definitions.Def_WeightedCache3SUM_Alias_fffbfb6b1f2e0917
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
theorem _root_.solution (k : ℕ) :
    Tendsto (fun n : ℕ => Real.log (falseNumerator k n : ℝ) / Real.log n) atTop
      (𝓝 (2 + (E + bandShift) / 5)) := by
  have h1 := nat_log_rate_mul candidateCount_log_rate rawTripleBound_log_rate (by
    filter_upwards [candidateCount_eventually_pos, eventually_ge_atTop (1 : ℕ)] with n hC hn
    exact ⟨hC, rawTripleBound_pos (by omega)⟩)
  have h2 := nat_log_rate_mul h1 (scoreLoss_log_ratio_tendsto_zero k) (by
    filter_upwards [candidateCount_eventually_pos, eventually_ge_atTop (1 : ℕ)] with n hC hn
    exact ⟨Nat.mul_pos hC (rawTripleBound_pos (by omega)), scoreLoss_pos k n⟩)
  have h3 := nat_log_rate_mul h2 primeLoss_log_ratio_tendsto_zero (by
    filter_upwards [candidateCount_eventually_pos, eventually_ge_atTop (1 : ℕ)] with n hC hn
    exact ⟨Nat.mul_pos (Nat.mul_pos hC (rawTripleBound_pos (by omega))) (scoreLoss_pos k n),
      primeLoss_pos n⟩)
  simpa only [falseNumerator, zero_add, add_zero] using h3
end ThreeSum.MassScales
