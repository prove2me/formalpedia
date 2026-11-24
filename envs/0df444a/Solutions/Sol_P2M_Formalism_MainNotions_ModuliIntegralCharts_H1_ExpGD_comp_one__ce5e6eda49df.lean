-- Prove2me | solution 1 for P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGD_comp_one__ce5e6eda49df
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:43.945706+00:00
-- url     : https://prove2.me/submissions/783c78a6-d0d9-4916-859c-e81caf5d0db1

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CocycleProductThree
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_JetPointZeroEqOne

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGD
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
attribute [local instance] Over.cartesianMonoidalCategory
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGD
theorem _root_.solution {X0 : Scheme.{0}} {G : Over X0} [GrpObj G] {T T' : Over X0} (f : T' ⟶ T) :
    f ≫ (1 : T ⟶ G) = 1 := by
  show f ≫ (toUnit T ≫ η[G]) = toUnit T' ≫ η[G]
  rw [← Category.assoc, toUnit_unique (f ≫ toUnit T) (toUnit T')]
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGD
