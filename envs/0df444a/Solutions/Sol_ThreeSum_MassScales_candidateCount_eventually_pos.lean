-- Prove2me | solution 1 for ThreeSum.MassScales.candidateCount_eventually_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:04:27.533781+00:00
-- url     : https://prove2.me/submissions/8366823e-1bfb-4803-8c66-dd071fb2edeb

import Definitions.Def_Submission_ThreeSum_HierarchyScales
import Definitions.Def_Submission_ThreeSum_MassScales
import Theorems.Thm_ThreeSum_Scales_actual_candidates_nonempty


set_option autoImplicit false
open ThreeSum ThreeSum.MassScales
open Filter Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.TrimScales
  ThreeSum.BandScales ThreeSum.CostLedger ThreeSum.HierarchyScales
open scoped Topology
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace ThreeSum.MassScales
theorem _root_.solution : ∀ᶠ n : ℕ in atTop, 0 < candidateCount n := by
  filter_upwards [actual_candidates_nonempty] with n hn
  exact Finset.card_pos.mpr hn
end ThreeSum.MassScales
