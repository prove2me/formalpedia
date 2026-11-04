-- Prove2me | solution 1 for ThreeSum.StageBounds.terminalChoices_log_rate_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:18:16.609731+00:00
-- url     : https://prove2.me/submissions/73cd1166-06c0-4837-ae04-6c2f5de4ea4b

import Definitions.Def_Submission_ThreeSum_MassScales
import Definitions.Def_Submission_ThreeSum_StageBounds
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_Scales_mu_log_ratio_tendsto
import Theorems.Thm_ThreeSum_Switch_mem_candidates
import Theorems.Thm_ThreeSum_Switch_residual_real_identity
import Definitions.Def_WeightedCache3SUM_Alias_d36ea36b26405845
import Theorems.Thm_ThreeSum_TrimScales_mu_tendsto_atTop
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.Switch.mem_candidates



set_option autoImplicit false
open ThreeSum ThreeSum.StageBounds
open Filter Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.TrimScales
  ThreeSum.BandScales ThreeSum.Switch ThreeSum.CostLedger ThreeSum.HierarchyScales
  ThreeSum.MassScales
open scoped Topology
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace ThreeSum.StageBounds
theorem _root_.solution :
    Tendsto (fun n : ℕ => Real.log (terminalChoices n : ℝ) / Real.log n) atTop
      (𝓝 ((1 - terminalFraction) / 5)) := by
  have hh := mu_log_ratio_tendsto.const_mul (Real.log 2 * (1 - terminalFraction))
  have heq : Real.log 2 * (1 - terminalFraction) * (1 / (5 * Real.log 2)) =
      (1 - terminalFraction) / 5 := by field_simp
  rw [heq] at hh
  apply hh.congr'
  filter_upwards [mu_tendsto_atTop.eventually (eventually_ge_atTop 1)] with n hn
  have hid := residual_real_identity (by omega : 0 < mu n)
    (j := terminalDepth n) le_rfl
  rw [terminal_fraction_exact (by omega : 0 < mu n)] at hid
  simp only [terminalChoices, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, hid]
  ring
end ThreeSum.StageBounds
