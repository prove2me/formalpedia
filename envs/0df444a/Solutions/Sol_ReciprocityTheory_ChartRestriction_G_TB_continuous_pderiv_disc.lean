-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.continuous_pderiv_disc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:33:18.906135+00:00
-- url     : https://prove2.me/submissions/310b0b64-7726-4ca9-9223-7497b385239d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ContinuousPderivDisc

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB
open scoped MvPowerSeries.WithPiTopology
namespace ReciprocityTheory.ChartRestriction.G.TB
theorem _root_.solution {σ R : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
    (i : σ) : Continuous (fun f : MvPowerSeries σ R => pderiv R i f) := by
  refine continuous_pi fun n => ?_
  have h : (fun f : MvPowerSeries σ R => (pderiv R i f) n) =
      (fun a : R => a * ((n i : R) + 1)) ∘ ⇑(MvPowerSeries.coeff (n + Finsupp.single i 1)) := by
    funext f
    exact MvPowerSeries.coeff_pderiv f n
  rw [h]
  exact continuous_of_discreteTopology.comp (MvPowerSeries.WithPiTopology.continuous_coeff R _)
end ReciprocityTheory.ChartRestriction.G.TB
