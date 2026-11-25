-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA.biext_change_second_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:24:46.487169+00:00
-- url     : https://prove2.me/submissions/d88f383c-a55b-4e32-ae65-a7551e98e491

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_BiextChangeSecondFactor
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_CVA_map_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA
variable {R k O : Type} [CommRing R] [CommRing k] [Algebra ℚ k] [Algebra R k] [CommRing O] [StarRing O] {d : ℕ}
variable {B : FB k d O} (t : IntTie (algebraMap R k) B) (hφ : Function.Injective (algebraMap R k))
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA
theorem _root_.solution : FB.toK k (fbOf t hφ).ph2 = FB.toK k B.ph2 := by
  show MvPowerSeries.map (algebraMap R k) t.ph2T = MvPowerSeries.map (algebraMap k k) B.ph2
  rw [map_self]
  exact t.h2
end ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA
