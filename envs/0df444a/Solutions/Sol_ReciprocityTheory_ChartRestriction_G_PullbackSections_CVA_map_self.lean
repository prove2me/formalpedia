-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA.map_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:45:30.757377+00:00
-- url     : https://prove2.me/submissions/a72d1547-37a9-4b40-98ac-04e17cfb6c94

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_BiextChangeSecondFactor

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
theorem _root_.solution {n : ℕ} (f : PS k n d) : MvPowerSeries.map (algebraMap k k) f = f := by
  ext n
  simp [MvPowerSeries.coeff_map]
end ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA
