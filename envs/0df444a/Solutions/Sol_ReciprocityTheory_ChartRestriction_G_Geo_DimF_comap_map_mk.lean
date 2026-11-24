-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.DimF.comap_map_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:58:43.56871+00:00
-- url     : https://prove2.me/submissions/7dfd06c6-820e-460a-96e7-04ea00149015

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.DimF
variable {A : Type*} [CommRing A]
namespace ReciprocityTheory.ChartRestriction.G.Geo.DimF
theorem _root_.solution {q M : Ideal A} (h : q ≤ M) :
    (M.map (Ideal.Quotient.mk q)).comap (Ideal.Quotient.mk q) = M := by
  exact Ideal.comap_map_mk h
end ReciprocityTheory.ChartRestriction.G.Geo.DimF
