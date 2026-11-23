-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.constantCoeff_psubst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:29:43.131574+00:00
-- url     : https://prove2.me/submissions/abcdd8ea-a119-492b-84a3-4a6b8c2f14ca

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
variable {k : Type} [CommRing k] [Algebra ℚ k] {σ : Type}
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
theorem _root_.solution {a : MvPowerSeries σ k} (ha : constantCoeff a = 0) (f : PowerSeries k) :
    constantCoeff (PowerSeries.subst a f) = PowerSeries.constantCoeff f := by
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero ha
  have h1 : f = PowerSeries.C (PowerSeries.constantCoeff f) +
      (f - PowerSeries.C (PowerSeries.constantCoeff f)) := by ring
  conv_lhs => rw [h1]
  rw [PowerSeries.subst_add hs, PowerSeries.subst_C, map_add,
    PowerSeries.constantCoeff_subst_eq_zero ha _ (by simp), add_zero]
  simp
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
