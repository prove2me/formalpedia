-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation.cQ_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:20.1074+00:00
-- url     : https://prove2.me/submissions/c7fd4c85-fe5e-46c1-af37-267b54dbee50

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdNeg

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
namespace ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
theorem _root_.solution (T : Over (Spec (CommRingCat.of R))) (a b : D.X) : cQ D T (a + b) = cQ D T a * cQ D T b := by
  unfold cQ
  rw [D.c_add, padd, ← Hom.mul_def, MonObj.comp_mul]
end ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
