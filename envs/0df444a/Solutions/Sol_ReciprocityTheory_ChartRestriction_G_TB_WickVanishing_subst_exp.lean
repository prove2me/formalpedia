-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.subst_exp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:37:36.161038+00:00
-- url     : https://prove2.me/submissions/ad847de8-7984-4dfc-a182-1d8d7d82e5c7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
theorem _root_.solution {k : Type} [CommRing k] [Algebra ℚ k] {σ τ : Type} [Finite σ] (φ : σ → MvPowerSeries τ k)
    (hφ : ∀ s, constantCoeff (φ s) = 0) {a : MvPowerSeries σ k} (ha : constantCoeff a = 0) :
    MvPowerSeries.subst φ (PowerSeries.subst a (PowerSeries.exp k)) =
      PowerSeries.subst (MvPowerSeries.subst φ a) (PowerSeries.exp k) := by
  have ha' := (PowerSeries.HasSubst.of_constantCoeff_zero ha).const
  exact MvPowerSeries.subst_comp_subst_apply ha' (MvPowerSeries.hasSubst_of_constantCoeff_zero hφ) _
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
