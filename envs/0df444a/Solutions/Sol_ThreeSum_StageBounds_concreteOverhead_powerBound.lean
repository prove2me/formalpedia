-- Prove2me | solution 1 for ThreeSum.StageBounds.concreteOverhead_powerBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:22:20.0924+00:00
-- url     : https://prove2.me/submissions/3ca73a20-f54f-4e8f-821b-2c4a9c3b3c2a

import Definitions.Def_Submission_ThreeSum_MassScales
import Definitions.Def_Submission_ThreeSum_StageBounds
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_of_rate
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_const
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_mul
import Definitions.Def_WeightedCache3SUM_Alias_851b6603dbe122fe
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_pow
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_HierarchyScales_polynomialFactor_log_rate
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_Scales_localSearch_subpolynomial
import Theorems.Thm_ThreeSum_Scales_primeWindow_log_ratio_tendsto_zero
import Theorems.Thm_ThreeSum_Switch_mem_candidates
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
theorem _root_.solution (C : ℕ) : PowerBound (concreteOverhead C) 0 := by
  have hl : PowerBound (localSearch C) 0 := by
    intro d hd
    simpa only [zero_add] using localSearch_subpolynomial C hd
  have hp := PowerBound.of_rate (polynomialFactor_log_rate C)
  have hw := ((PowerBound.of_rate primeWindow_log_ratio_tendsto_zero).add_same (PowerBound.const 1)).pow C
  intro d hd
  have hh := (((hl.add_same (PowerBound.const 1)).mul hw).mul hp) d hd
  simpa only [concreteOverhead, mul_zero, zero_add] using hh
end ThreeSum.StageBounds
