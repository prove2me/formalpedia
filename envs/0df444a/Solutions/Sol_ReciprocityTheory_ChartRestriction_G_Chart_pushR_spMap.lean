-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.pushR_spMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:57:37.410049+00:00
-- url     : https://prove2.me/submissions/78d11b50-1630-4997-be29-25b5bbeace88

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_AlgChart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsUnivRingBc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pushR_left

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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
variable {P : Type} [CommRing P] [Algebra R' P] [Algebra R P] [IsScalarTower R R' P]
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution {P' : Type} [CommRing P'] [Algebra R' P'] [Algebra R P'] [IsScalarTower R R' P'] (g : P →ₐ[R'] P')
    (y : sp (R₀ := R') P ⟶ (Over.pullback (fB R R')).obj G) :
    pushR G (spMap g ≫ y) = spMap (g.restrictScalars R) ≫ pushR G y := by
  apply Over.OverMorphism.ext
  rw [pushR_left, Over.comp_left, Over.comp_left, pushR_left, Category.assoc]
  rfl
end ReciprocityTheory.ChartRestriction.G.Chart
