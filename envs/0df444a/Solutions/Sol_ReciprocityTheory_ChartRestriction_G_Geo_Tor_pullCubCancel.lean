-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.pullCubCancel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:38:12.036391+00:00
-- url     : https://prove2.me/submissions/164c9ae0-9900-4bd3-aeea-cfbc5e3303b0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArcSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_cancel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_pgen_cancel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_pmaps_cancel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isPullCubical_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution : PullCubCancelSt := by
  intro S S' S'' G G' G'' _ _ _ _ _ _ m m' n L L' L'' c c' c'' hF hF3 he hm hn
  obtain ⟨nF, nF3, ne, hne, hnp⟩ := n
  dsimp only at hF hF3 he
  subst hF hF3 he
  rw [isPullCubical_iff] at hm hn ⊢
  obtain ⟨w, hw, hr, ht⟩ := hm
  obtain ⟨w'', hw'', hr'', ht''⟩ := hn
  obtain ⟨w', T⟩ := exists_cancel L.isLB w w'' hw hw'' L'.isLB L''.isLB
  exact ⟨w', T.pgen_cancel L.isLB hw hw'', T.pmaps_cancel L.isLB (fun _ => m'.e_comm) hr hr'',
    T.pmaps_cancel L.isLB (fun I => m'.psum_comm I.down) ht ht''⟩
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
