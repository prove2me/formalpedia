-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.pullCubComp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:30:48.38402+00:00
-- url     : https://prove2.me/submissions/25fc1471-be8d-4613-9efa-55528168839b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArcSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_pgen_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_pmaps_comp
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
theorem _root_.solution : PullCubCompSt := by
  intro S S' S'' G G' G'' _ _ _ _ _ _ m m' n L L' L'' c c' c'' hF hF3 he hm hm'
  obtain ⟨nF, nF3, ne, hne, hnp⟩ := n
  dsimp only at hF hF3 he
  subst hF hF3 he
  rw [isPullCubical_iff] at hm hm' ⊢
  obtain ⟨w, hw, hr, ht⟩ := hm
  obtain ⟨w', hw', hr', ht'⟩ := hm'
  obtain ⟨w'', T⟩ := exists_comp L'.isLB w w' hw hw' L.isLB L''.isLB
  exact ⟨w'', T.pgen_comp L'.isLB hw hw', T.pmaps_comp L'.isLB (fun _ => m'.e_comm) hr hr',
    T.pmaps_comp L'.isLB (fun I => m'.psum_comm I.down) ht ht'⟩
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
