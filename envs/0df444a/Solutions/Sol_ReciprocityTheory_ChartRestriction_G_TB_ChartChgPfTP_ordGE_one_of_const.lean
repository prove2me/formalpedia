-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP.ordGE_one_of_const
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:05:27.944055+00:00
-- url     : https://prove2.me/submissions/392b7cf1-87cd-478a-8287-49e116f3bea9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChgPfTP

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
open ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP
variable {k : Type} [CommRing k]
namespace ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP
theorem _root_.solution {σ : Type} {A : MvPowerSeries σ k} (h : constantCoeff A = 0) : OrdGE 1 A := by
  intro e he
  have he0 : e = 0 := by
    first
    | exact (Finsupp.degree_eq_zero_iff e).mp (by omega)
    | exact Finsupp.degree_eq_zero_iff.mp (by omega)
  subst he0
  first
  | (rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]; exact h)
  | simpa using h
end ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP
