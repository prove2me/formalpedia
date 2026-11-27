-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.anFB_canon
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:28:39.086011+00:00
-- url     : https://prove2.me/submissions/a8b244ab-5b21-43c4-9594-d22069ff7b94

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnHolFamOfHolTo
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_ComposeLinearAction
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_expS_zero_an
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_PullbackSections_ev_zero__ee2e67940270


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ NumberField
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g n : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution [StarRing (𝓞 E)] (ty : Fin g → (E →+* ℂ)) : (anFB ty).IsCanonGauge ℂ 0 where
  ax0 := ev_zero' _
  ax1 := ev_zero' _
  ph1 := by simp [anFB, FB.triv, ev_zero', expS_zero_an]
  ph2 := by simp [anFB, FB.triv, ev_zero', expS_zero_an]
  sy := by simp [anFB, FB.triv, ev_zero', expS_zero_an]
  ad a := by simp [anFB, FB.triv, ev_zero', expS_zero_an]
end ReciprocityTheory.ChartRestriction.G.PullbackSections
