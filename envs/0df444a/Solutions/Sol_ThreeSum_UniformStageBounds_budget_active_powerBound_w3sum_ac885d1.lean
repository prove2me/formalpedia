-- Prove2me | solution 1 for ThreeSum.UniformStageBounds.budget_active_powerBound_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:03:17.759361+00:00
-- url     : https://prove2.me/submissions/3c2ad90b-32f3-4eea-92a8-d521fd1d07de

import Definitions.Def_Submission_ThreeSum_StageBounds
import Definitions.Def_Submission_ThreeSum_UniformStageBounds
import Theorems.Thm_ThreeSum_UniformStageBounds_falseBudget_powerBound
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_HierarchyScales_allQueryTerms_eventually_le
import Theorems.Thm_ThreeSum_HierarchyScales_microPartitions_subpolynomial
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_mul
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_of_rate
import Theorems.Thm_ThreeSum_Switch_mem_candidates
import Definitions.Def_WeightedCache3SUM_Alias_dc2f19a97a662b74
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.Switch.mem_candidates



set_option autoImplicit false
open ThreeSum ThreeSum.UniformStageBounds
open Filter Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.TrimScales
  ThreeSum.BandScales ThreeSum.Switch ThreeSum.CostLedger ThreeSum.HierarchyScales
  ThreeSum.MassScales ThreeSum.StageBounds
open scoped Topology
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace ThreeSum.UniformStageBounds
theorem _root_.solution (k : ℕ) :
    PowerBound (activeCount (falseBudget k))
      (2 - epsilon * (1 / 2 - bandShift - kappa - entropyRatio * (1 + boxSaving - 2 * bandShift))) := by
  have hG : PowerBound microPartitions 0 := by
    intro d hd
    simpa only [zero_add] using microPartitions_subpolynomial hd
  have hQ : PowerBound allQueryTerms ((entropyRatio * (1 + boxSaving - 2 * bandShift)) / 5) :=
    fun _ hd => allQueryTerms_eventually_le hd
  have hh := (((falseBudget_powerBound k).mul
    (PowerBound.of_rate representationBound_log_rate)).mul hG).mul hQ
  have heq : ((2 - (1 / 2 - bandShift) / 5) + kappa / 5 + 0) +
      (entropyRatio * (1 + boxSaving - 2 * bandShift)) / 5 =
      2 - epsilon * (1 / 2 - bandShift - kappa - entropyRatio * (1 + boxSaving - 2 * bandShift)) := by
    unfold epsilon
    ring
  rw [heq] at hh
  exact hh
end ThreeSum.UniformStageBounds
