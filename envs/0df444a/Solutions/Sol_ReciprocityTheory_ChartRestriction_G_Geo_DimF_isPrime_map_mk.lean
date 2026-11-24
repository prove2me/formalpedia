-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.DimF.isPrime_map_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:17:59.923177+00:00
-- url     : https://prove2.me/submissions/ffc21786-9dfd-4cda-9e77-a76ef35d568c

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
theorem _root_.solution {q M : Ideal A} [M.IsPrime] (h : q ≤ M) :
    (M.map (Ideal.Quotient.mk q)).IsPrime :=
  Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact h)
end ReciprocityTheory.ChartRestriction.G.Geo.DimF
