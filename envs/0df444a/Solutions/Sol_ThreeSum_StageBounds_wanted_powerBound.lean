-- Prove2me | solution 1 for ThreeSum.StageBounds.wanted_powerBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:53:00.32621+00:00
-- url     : https://prove2.me/submissions/57691408-83d8-45bf-8c92-a0015be27c63

import Definitions.Def_Submission_ThreeSum_MassScales
import Definitions.Def_Submission_ThreeSum_StageBounds
import Theorems.Thm_ThreeSum_MassScales_wantedMajorant_eventually_le
import Theorems.Thm_ThreeSum_MassScales_wanted_mass_le


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
theorem _root_.solution {W : ℕ → ℕ}
    (hW : ∀ᶠ n : ℕ in atTop, W n * radix n ≤ wantedNumerator n) :
    PowerBound W (2 - (1 / 2 + bandShift) / 5) := by
  intro d hd
  filter_upwards [hW, wantedMajorant_eventually_le hd] with n hn he
  exact (wanted_mass_le hn).trans he
end ThreeSum.StageBounds
