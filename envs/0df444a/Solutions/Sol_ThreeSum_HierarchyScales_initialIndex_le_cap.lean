-- Prove2me | solution 1 for ThreeSum.HierarchyScales.initialIndex_le_cap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:51:25.377783+00:00
-- url     : https://prove2.me/submissions/5a19ad8b-25bc-4acc-b6ce-d5971d878c48

import Definitions.Def_Submission_ThreeSum_CostLedger
import Definitions.Def_Submission_ThreeSum_HierarchyScales
import Theorems.Thm_ThreeSum_HierarchyScales_initialCap_bounds
import Theorems.Thm_ThreeSum_HierarchyScales_initialCap_accepted
import Theorems.Thm_ThreeSum_PrimeDensity_mem_candidates
import Theorems.Thm_ThreeSum_Switch_mem_candidates
import Theorems.Thm_ThreeSum_Switch_switchIndex_le
attribute [local simp] ThreeSum.Switch.mem_candidates



set_option autoImplicit false
open ThreeSum ThreeSum.HierarchyScales
open Filter Set Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.Switch ThreeSum.CostLedger
open scoped Topology BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace ThreeSum.HierarchyScales
theorem _root_.solution (J : ℕ) {r : ℕ} (hr : 50 ≤ r) :
    switchIndex J 0 r ≤ initialCap r := by
  apply switchIndex_le
  apply mem_candidates.mpr
  refine ⟨?_, initialCap_accepted J r⟩
  have h := (initialCap_bounds r).2
  omega
end ThreeSum.HierarchyScales
