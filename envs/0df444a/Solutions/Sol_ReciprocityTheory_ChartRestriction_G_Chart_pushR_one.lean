-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.pushR_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:06:57.813733+00:00
-- url     : https://prove2.me/submissions/9ca69d39-93b3-439c-840c-6d58f067026c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_AlgChart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsUnivRingBc
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
theorem _root_.solution : pushR G (1 : sp (R₀ := R') P ⟶ (Over.pullback (fB R R')).obj G) = 1 := by
  have hw := (isGrpPullback_pullback G (fB R R')).1.w
  have hmul : ∀ x y : sp (R₀ := R') P ⟶ (Over.pullback (fB R R')).obj G,
      pushR G (x * y) = pushR G x * pushR G y := by
    intro x y
    have hpp : pushPt hw (x * y) = pushPt hw x * pushPt hw y := by
      apply Over.OverMorphism.ext
      exact ((isGrpPullback_pullback G (fB R R')).2 _ x y (pushPt hw x) (pushPt hw y) rfl rfl).symm
    simp only [pushR]
    rw [hpp, MonObj.comp_mul]
  have h1 : pushR G (1 : sp (R₀ := R') P ⟶ (Over.pullback (fB R R')).obj G) *
      pushR G (1 : sp (R₀ := R') P ⟶ (Over.pullback (fB R R')).obj G) =
      pushR G (1 : sp (R₀ := R') P ⟶ (Over.pullback (fB R R')).obj G) := by
    rw [← hmul, _root_.mul_one]
  exact mul_eq_left.mp h1
end ReciprocityTheory.ChartRestriction.G.Chart
