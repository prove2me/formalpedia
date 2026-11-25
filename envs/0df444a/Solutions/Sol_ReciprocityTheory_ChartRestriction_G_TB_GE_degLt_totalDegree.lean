-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.GE.degLt_totalDegree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:31:20.644795+00:00
-- url     : https://prove2.me/submissions/602bf281-301d-4b48-a1a5-dd5239e9b5c3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.GE
variable {k : Type} [CommRing k] {d : ℕ}
variable {ι : Type} [Fintype ι]
namespace ReciprocityTheory.ChartRestriction.G.TB.GE
theorem _root_.solution (P : MvPolynomial ι k) : DegLt (P.totalDegree + 1) P := by
  intro m hm
  by_contra hne
  have hmem : m ∈ P.support := MvPolynomial.mem_support_iff.mpr hne
  have h1 : m.degree ≤ P.totalDegree := by
    first
    | exact MvPolynomial.le_totalDegree hmem
    | simpa [Finsupp.degree, Finsupp.sum] using MvPolynomial.le_totalDegree hmem
  omega
end ReciprocityTheory.ChartRestriction.G.TB.GE
