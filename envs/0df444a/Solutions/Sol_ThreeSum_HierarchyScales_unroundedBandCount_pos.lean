-- Prove2me | solution 1 for ThreeSum.HierarchyScales.unroundedBandCount_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:18:50.873453+00:00
-- url     : https://prove2.me/submissions/661d521c-21ae-456e-a106-19c01b17c8ca

import Definitions.Def_Submission_ThreeSum_CostLedger
import Definitions.Def_Submission_ThreeSum_HierarchyScales
import Theorems.Thm_ThreeSum_BandScales_bandSize_pos


set_option autoImplicit false
open ThreeSum ThreeSum.HierarchyScales
open Filter Set Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.Switch ThreeSum.CostLedger
open scoped Topology BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace ThreeSum.HierarchyScales
theorem _root_.solution {n : ℕ} (hn : 0 < n) : 0 < unroundedBandCount n := by
  exact div_pos (by exact_mod_cast hn) (by exact_mod_cast BandScales.bandSize_pos n)
end ThreeSum.HierarchyScales
