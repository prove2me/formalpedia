-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation.gs_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:40:08.999079+00:00
-- url     : https://prove2.me/submissions/698ce951-2cbb-446e-b55b-5d9960235578

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_GenCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_AppCompatGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation

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
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing
variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]
namespace ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
theorem _root_.solution (f : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : f z ∈ U) {n : ℕ} (a : Fin n → Γ(Y, U)) :
    gs f z U (∑ i, a i) = ∑ i, gs f z U (a i) := by
  rw [gs_eq f z U h, map_sum, map_sum]
  exact Finset.sum_congr rfl fun i _ => (gs_eq f z U h (a i)).symm
end ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
