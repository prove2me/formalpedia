-- Prove2me | solution 1 for ThreeSum.HierarchyScales.microPartitions_subpolynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:11:52.641061+00:00
-- url     : https://prove2.me/submissions/1f8d3bf9-5096-4e3a-9e96-ed0844f1e12f

import Definitions.Def_Submission_ThreeSum_CostLedger
import Definitions.Def_Submission_ThreeSum_HierarchyScales
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_Scales_localSearch_subpolynomial
import Theorems.Thm_ThreeSum_Scales_muZero_tendsto_atTop
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
theorem _root_.solution {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, (microPartitions n : ℝ) ≤ (n : ℝ) ^ d := by
  filter_upwards [localSearch_subpolynomial 1 hd,
    muZero_tendsto_atTop.eventually (eventually_ge_atTop 1)] with n hn hmu
  have hpow : muZero n ≤ muZero n ^ 2 := by nlinarith
  have hc : microPartitions n ≤ localSearch 1 n := by
    exact (Nat.choose_le_two_pow _ _).trans (by simpa [localSearch] using Nat.pow_le_pow_right (by norm_num : 0 < 2) hpow)
  exact (show (microPartitions n : ℝ) ≤ localSearch 1 n by exact_mod_cast hc).trans hn
end ThreeSum.HierarchyScales
