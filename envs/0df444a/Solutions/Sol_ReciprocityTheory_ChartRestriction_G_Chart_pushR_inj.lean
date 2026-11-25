-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.pushR_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:57:32.164955+00:00
-- url     : https://prove2.me/submissions/e5841df5-f538-4343-944d-d27027986dd6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_AlgChart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsUnivRingBc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pushR_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_pullback


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
theorem _root_.solution {y y' : sp (R₀ := R') P ⟶ (Over.pullback (fB R R')).obj G} (h : pushR G y = pushR G y') :
    y = y' := by
  have h1 : (pushR G y).left = (pushR G y').left := by rw [h]
  rw [pushR_left, pushR_left] at h1
  apply Over.OverMorphism.ext
  exact (isGrpPullback_pullback G (fB R R')).1.hom_ext h1 ((Over.w y).trans (Over.w y').symm)
end ReciprocityTheory.ChartRestriction.G.Chart
