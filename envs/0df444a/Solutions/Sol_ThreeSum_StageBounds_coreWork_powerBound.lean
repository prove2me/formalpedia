-- Prove2me | solution 1 for ThreeSum.StageBounds.coreWork_powerBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:05:56.635059+00:00
-- url     : https://prove2.me/submissions/3dd07af4-f8ad-422d-9011-64dcdf400289

import Definitions.Def_Submission_ThreeSum_MassScales
import Definitions.Def_Submission_ThreeSum_StageBounds
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_mono_exponent
import Definitions.Def_WeightedCache3SUM_Alias_851b6603dbe122fe
import Theorems.Thm_ThreeSum_StageBounds_table_powerBound
import Theorems.Thm_ThreeSum_StageBounds_encoder_powerBound
import Theorems.Thm_ThreeSum_StageBounds_boxes_powerBound
import Theorems.Thm_ThreeSum_StageBounds_initial_powerBound
import Theorems.Thm_ThreeSum_StageBounds_active_powerBound
import Theorems.Thm_ThreeSum_StageBounds_terminal_powerBound
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_Parameters_all_costs_le_certificate
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
theorem _root_.solution {W H P H1 : ℕ → ℕ} (k : ℕ)
    (hW : ∀ᶠ n : ℕ in atTop, W n * radix n ≤ wantedNumerator n)
    (hscore : ∀ᶠ n : ℕ in atTop, P n * H n ≤ scoreLoss k n * H1 n)
    (hinit : ∀ᶠ n : ℕ in atTop, H1 n ≤ candidateCount n * rawTripleBound n)
    (hmod : ∀ᶠ n : ℕ in atTop, radix n ≤ primeLoss radix n * P n) :
    PowerBound (coreWork W H) certificateExponent := by
  have ht := table_powerBound.mono_exponent
    (all_costs_le_certificate _ (by simp [costLedger]))
  have he := encoder_powerBound.mono_exponent
    (all_costs_le_certificate _ (by simp [costLedger]))
  have hb := boxes_powerBound.mono_exponent
    (all_costs_le_certificate _ (by simp [costLedger]))
  have hi := (initial_powerBound hW).mono_exponent
    (all_costs_le_certificate _ (by simp [costLedger]))
  have ha := (active_powerBound k hscore hinit hmod).mono_exponent
    (all_costs_le_certificate _ (by simp [costLedger]))
  have hf := (terminal_powerBound k hscore hinit hmod).mono_exponent
    (all_costs_le_certificate _ (by simp [costLedger]))
  exact ((((ht.add_same he).add_same hb).add_same hi).add_same ha).add_same hf
end ThreeSum.StageBounds
