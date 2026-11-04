-- Prove2me | solution 1 for ThreeSum.UniformStageBounds.budget_core_powerBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:09:31.187165+00:00
-- url     : https://prove2.me/submissions/d9bfe481-e4b2-4c0c-b9e7-e17137b66681

import Definitions.Def_Submission_ThreeSum_StageBounds
import Definitions.Def_Submission_ThreeSum_UniformStageBounds
import Theorems.Thm_ThreeSum_UniformStageBounds_budget_initial_powerBound
import Definitions.Def_WeightedCache3SUM_Alias_c8a0964bc436b6dc
import Theorems.Thm_ThreeSum_UniformStageBounds_budget_terminal_powerBound
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_Parameters_all_costs_le_certificate
import Definitions.Def_WeightedCache3SUM_Alias_851b6603dbe122fe
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_mono_exponent
import Theorems.Thm_ThreeSum_StageBounds_boxes_powerBound
import Theorems.Thm_ThreeSum_StageBounds_encoder_powerBound
import Theorems.Thm_ThreeSum_StageBounds_table_powerBound
import Theorems.Thm_ThreeSum_Switch_mem_candidates
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
    PowerBound (coreWork wantedBudget (falseBudget k)) certificateExponent := by
  have ht := table_powerBound.mono_exponent
    (all_costs_le_certificate _ (by simp [costLedger]))
  have he := encoder_powerBound.mono_exponent
    (all_costs_le_certificate _ (by simp [costLedger]))
  have hb := boxes_powerBound.mono_exponent
    (all_costs_le_certificate _ (by simp [costLedger]))
  have hi := budget_initial_powerBound.mono_exponent
    (all_costs_le_certificate _ (by simp [costLedger]))
  have ha := (budget_active_powerBound k).mono_exponent
    (all_costs_le_certificate _ (by simp [costLedger]))
  have hf := (budget_terminal_powerBound k).mono_exponent
    (all_costs_le_certificate _ (by simp [costLedger]))
  exact ((((ht.add_same he).add_same hb).add_same hi).add_same ha).add_same hf
end ThreeSum.UniformStageBounds
