-- Prove2me | solution 1 for ThreeSum.MassScales.rawTripleBound_log_rate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:46:14.604523+00:00
-- url     : https://prove2.me/submissions/dad108cd-f2ed-406e-85dd-c133a198c32f

import Definitions.Def_Submission_ThreeSum_HierarchyScales
import Definitions.Def_Submission_ThreeSum_MassScales
import Theorems.Thm_ThreeSum_MassScales_bandCount_pos
import Theorems.Thm_ThreeSum_MassScales_nat_log_rate_const
import Theorems.Thm_ThreeSum_MassScales_nat_log_rate_mul
import Theorems.Thm_ThreeSum_MassScales_nat_log_rate_pow
import Theorems.Thm_ThreeSum_MassScales_bandSize_log_rate_shift
import Theorems.Thm_ThreeSum_BandScales_bandSize_pos
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Definitions.Def_WeightedCache3SUM_Alias_79670fd38525811b
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
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
    Tendsto (fun n : ℕ => Real.log (rawTripleBound n : ℝ) / Real.log n) atTop
      (𝓝 (2 + (E + bandShift) / 5)) := by
  have h1 := nat_log_rate_mul (nat_log_rate_const 3) (nat_log_rate_pow bandCount_log_rate 2) (by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact ⟨by norm_num, Nat.pow_pos (bandCount_pos (by omega))⟩)
  have h2 := nat_log_rate_mul h1 (nat_log_rate_pow bandSize_log_rate_shift 3) (by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact ⟨Nat.mul_pos (by norm_num) (Nat.pow_pos (bandCount_pos (by omega))),
      Nat.pow_pos (bandSize_pos n)⟩)
  convert h2 using 1 <;> simp only [rawTripleBound, Nat.cast_ofNat] <;> ring
end ThreeSum.MassScales
