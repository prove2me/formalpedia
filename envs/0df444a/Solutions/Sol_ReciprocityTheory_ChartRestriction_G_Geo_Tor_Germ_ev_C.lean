-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.ev_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:18:51.671858+00:00
-- url     : https://prove2.me/submissions/73e1f648-3b8c-478b-8793-7cd9d827c092

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
theorem _root_.solution {m n : ℕ} (a : Fin m → Pt R n d) (r : R) : ev a (C r : PS R m d) = C r := by
  unfold ev MvPowerSeries.subst
  letI : UniformSpace R := ⊥
  first
  | (open MvPowerSeries.WithPiTopology in rw [MvPowerSeries.eval₂_C])
  | erw [MvPowerSeries.eval₂_C]
  all_goals first
    | rfl
    | simp [MvPowerSeries.algebraMap_apply]
end ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
