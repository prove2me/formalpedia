-- Prove2me | solution 1 for ThreeSum.HierarchyScales.unroundedBandCount_eventually_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:33:36.705203+00:00
-- url     : https://prove2.me/submissions/6b01427a-0069-46a5-9044-15efd7d0b418

import Definitions.Def_Submission_ThreeSum_CostLedger
import Definitions.Def_Submission_ThreeSum_HierarchyScales
import Theorems.Thm_ThreeSum_HierarchyScales_unroundedBandCount_pos
import Theorems.Thm_ThreeSum_HierarchyScales_unroundedBandCount_log_rate
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_Parameters_E_bounds
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
theorem _root_.solution :
    ∀ᶠ n : ℕ in atTop, 1 ≤ unroundedBandCount n := by
  have ha : (0 : ℝ) < 1 - (E + bandShift) / 5 := by
    have he := E_bounds.2
    dsimp [bandShift]
    linarith
  have hs := unroundedBandCount_log_rate.eventually (lt_mem_nhds ha)
  filter_upwards [hs, eventually_ge_atTop (2 : ℕ)] with n hn hge
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hb : 0 < Real.log (unroundedBandCount n) := (div_pos_iff.mp hn).elim
    (fun h => h.1) (fun h => False.elim (not_lt_of_ge hlog.le h.2))
  exact ((Real.log_pos_iff (unroundedBandCount_pos (by omega : 0 < n)).le).mp hb).le
end ThreeSum.HierarchyScales
