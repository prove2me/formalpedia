-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA.fbOf_toKad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:24:51.879667+00:00
-- url     : https://prove2.me/submissions/66896d32-704d-4e4d-8b4e-b1403e13f9fe

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
theorem _root_.solution (a : O) : FB.toK k ((fbOf t hφ).ad a) = FB.toK k (B.ad a) := by
  show MvPowerSeries.map (algebraMap R k) (t.adT a) = MvPowerSeries.map (algebraMap k k) (B.ad a)
  rw [map_self]
  exact t.had a
end ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA
