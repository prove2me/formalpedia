-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.ev_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:17:17.979466+00:00
-- url     : https://prove2.me/submissions/049421ea-d7d1-47a3-8933-b5a04aec497e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasSubstEv

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
open MvPowerSeries
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {R : Type} [CommRing R] {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
theorem _root_.solution {m n : ℕ} (a : Fin m → Pt R n d) (h : ∀ j i, constantCoeff (a j i) = 0)
    (f g : PS R m d) : ev a (f * g) = ev a f * ev a g := by
  unfold ev
  exact MvPowerSeries.subst_mul (hasSubst_ev a h) f g
end ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
